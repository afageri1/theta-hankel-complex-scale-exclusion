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
theorem hpThetaDensityExpCompact_cell200 :
    ∀ t ∈ Set.Icc ((81 / 640) : ℝ) (2029 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((80502767 / 62500000) : ℝ) ≤ Real.exp (2 * (81 / 640)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (81 / 640)) (80502767 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2029 / 16000) : ℝ)) ≤ (161086057 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2029 / 16000)) (161086057 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((187057516917 / 1000000) : ℝ) ≤ Real.exp (3 * (4046391 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4046391 / 1000000)) (187057516917 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((81 / 640) : ℝ) (2029 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4046391 / 1000000) (126517 / 31250) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (81 / 640) (2029 / 16000) (80502767 / 62500000) (161086057 / 125000000) (4046391 / 1000000) (126517 / 31250) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (81 / 640) (2029 / 16000) (4046391 / 1000000) (126517 / 31250) (41201 / 1000) (8257 / 200)
    (24749 / 250) (50199 / 500) (-569089 / 1000) (182359 / 1000000) (2149243 / 500) (342141 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4046391 / 1000000) (187057516917 / 1000000) (342141 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4046391 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4046391 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell201 :
    ∀ t ∈ Set.Icc ((2029 / 16000) : ℝ) (2033 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((257737691 / 200000000) : ℝ) ≤ Real.exp (2 * (2029 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2029 / 16000)) (257737691 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2033 / 16000) : ℝ)) ≤ (1289332961 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2033 / 16000)) (1289332961 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((188196217851 / 1000000) : ℝ) ≤ Real.exp (3 * (2024207 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2024207 / 500000)) (188196217851 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2029 / 16000) : ℝ) (2033 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2024207 / 500000) (4050569 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2029 / 16000) (2033 / 16000) (257737691 / 200000000) (1289332961 / 1000000000) (2024207 / 500000) (4050569 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2029 / 16000) (2033 / 16000) (2024207 / 500000) (4050569 / 1000000) (8251 / 200) (20669 / 500)
    (99329 / 1000) (50367 / 500) (-568987 / 1000) (181527 / 1000000) (1076773 / 250) (1360283 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2024207 / 500000) (188196217851 / 1000000) (1360283 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2024207 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2024207 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell202 :
    ∀ t ∈ Set.Icc ((2033 / 16000) : ℝ) (2037 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((8058331 / 6250000) : ℝ) ≤ Real.exp (2 * (2033 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2033 / 16000)) (8058331 / 6250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2037 / 16000) : ℝ)) ≤ (1289977789 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2037 / 16000)) (1289977789 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((94671493289 / 500000) : ℝ) ≤ Real.exp (3 * (4050439 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4050439 / 1000000)) (94671493289 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2033 / 16000) : ℝ) (2037 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4050439 / 1000000) (810519 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2033 / 16000) (2037 / 16000) (8058331 / 6250000) (1289977789 / 1000000000) (4050439 / 1000000) (810519 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2033 / 16000) (2037 / 16000) (4050439 / 1000000) (810519 / 200000) (10327 / 250) (5174 / 125)
    (12458 / 125) (101071 / 1000) (-568887 / 1000) (180699 / 1000000) (1078929 / 250) (338011 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4050439 / 1000000) (94671493289 / 500000) (338011 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4050439 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4050439 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell203 :
    ∀ t ∈ Set.Icc ((2037 / 16000) : ℝ) (2041 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((322494447 / 250000000) : ℝ) ≤ Real.exp (2 * (2037 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2037 / 16000)) (322494447 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2041 / 16000) : ℝ)) ≤ (1290622939 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2041 / 16000)) (1290622939 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((190497314571 / 1000000) : ℝ) ≤ Real.exp (3 * (810493 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (810493 / 200000)) (190497314571 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2037 / 16000) : ℝ) (2041 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (810493 / 200000) (2027311 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2037 / 16000) (2041 / 16000) (322494447 / 250000000) (1290622939 / 1000000000) (810493 / 200000) (2027311 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2037 / 16000) (2041 / 16000) (810493 / 200000) (2027311 / 500000) (20681 / 500) (20723 / 500)
    100 (12676 / 125) (-113757 / 200) (179873 / 1000000) (4324357 / 1000) (1343851 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (810493 / 200000) (190497314571 / 1000000) (1343851 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (810493 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (810493 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell204 :
    ∀ t ∈ Set.Icc ((2041 / 16000) : ℝ) (409 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((645311469 / 500000000) : ℝ) ≤ Real.exp (2 * (2041 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2041 / 16000)) (645311469 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((409 / 3200) : ℝ)) ≤ (322817103 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (409 / 3200)) (322817103 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((38331735977 / 200000) : ℝ) ≤ Real.exp (3 * (4054491 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4054491 / 1000000)) (38331735977 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2041 / 16000) : ℝ) (409 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4054491 / 1000000) (4056649 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2041 / 16000) (409 / 3200) (645311469 / 500000000) (322817103 / 250000000) (4054491 / 1000000) (4056649 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2041 / 16000) (409 / 3200) (4054491 / 1000000) (4056649 / 1000000) (8283 / 200) (41499 / 1000)
    (12542 / 125) (50873 / 500) (-568679 / 1000) (44763 / 250000) (4333011 / 1000) (333927 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4054491 / 1000000) (38331735977 / 200000) (333927 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4054491 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4054491 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell205 :
    ∀ t ∈ Set.Icc ((409 / 3200) : ℝ) (2049 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1291268411 / 1000000000) : ℝ) ≤ Real.exp (2 * (409 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (409 / 3200)) (1291268411 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2049 / 16000) : ℝ)) ≤ (40372319 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2049 / 16000)) (40372319 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((38565656477 / 200000) : ℝ) ≤ Real.exp (3 * (4056519 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4056519 / 1000000)) (38565656477 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((409 / 3200) : ℝ) (2049 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4056519 / 1000000) (2029339 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (409 / 3200) (2049 / 16000) (1291268411 / 1000000000) (40372319 / 31250000) (4056519 / 1000000) (2029339 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (409 / 3200) (2049 / 16000) (4056519 / 1000000) (2029339 / 500000) (41469 / 1000) (41553 / 1000)
    (100673 / 1000) (20417 / 200) (-56857 / 100) (178233 / 1000000) (2170843 / 500) (1327607 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4056519 / 1000000) (38565656477 / 200000) (1327607 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4056519 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4056519 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell206 :
    ∀ t ∈ Set.Icc ((2049 / 16000) : ℝ) (2053 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1291914207 / 1000000000) : ℝ) ≤ Real.exp (2 * (2049 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2049 / 16000)) (1291914207 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2053 / 16000) : ℝ)) ≤ (646280163 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2053 / 16000)) (646280163 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((194005604401 / 1000000) : ℝ) ≤ Real.exp (3 * (1014637 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1014637 / 250000)) (194005604401 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2049 / 16000) : ℝ) (2053 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1014637 / 250000) (1015177 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2049 / 16000) (2053 / 16000) (1291914207 / 1000000000) (646280163 / 500000000) (1014637 / 250000) (1015177 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2049 / 16000) (2053 / 16000) (1014637 / 250000) (1015177 / 250000) (20761 / 500) (41607 / 1000)
    (10101 / 100) (12803 / 125) (-284229 / 500) (177417 / 1000000) (4350379 / 1000) (26391 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1014637 / 250000) (194005604401 / 1000000) (26391 / 20000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1014637 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1014637 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell207 :
    ∀ t ∈ Set.Icc ((2053 / 16000) : ℝ) (2057 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((51702413 / 40000000) : ℝ) ≤ Real.exp (2 * (2053 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2053 / 16000)) (51702413 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2057 / 16000) : ℝ)) ≤ (80825423 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2057 / 16000)) (80825423 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3903814003 / 20000) : ℝ) ≤ Real.exp (3 * (2030289 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2030289 / 500000)) (3903814003 / 20000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2053 / 16000) : ℝ) (2057 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2030289 / 500000) (4062739 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2053 / 16000) (2057 / 16000) (51702413 / 40000000) (80825423 / 62500000) (2030289 / 500000) (4062739 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2053 / 16000) (2057 / 16000) (2030289 / 500000) (4062739 / 1000000) (5197 / 125) (2083 / 50)
    (101349 / 1000) (25691 / 250) (-284171 / 500) (35321 / 200000) (4359089 / 1000) (655769 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2030289 / 500000) (3903814003 / 20000) (655769 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2030289 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2030289 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell208 :
    ∀ t ∈ Set.Icc ((2057 / 16000) : ℝ) (2061 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1293206767 / 1000000000) : ℝ) ≤ Real.exp (2 * (2057 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2057 / 16000)) (1293206767 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2061 / 16000) : ℝ)) ≤ (1293853533 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2061 / 16000)) (1293853533 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((196383624249 / 1000000) : ℝ) ≤ Real.exp (3 * (4062609 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4062609 / 1000000)) (196383624249 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2057 / 16000) : ℝ) (2061 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4062609 / 1000000) (4064771 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2057 / 16000) (2061 / 16000) (1293206767 / 1000000000) (1293853533 / 1000000000) (4062609 / 1000000) (4064771 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2057 / 16000) (2061 / 16000) (4062609 / 1000000) (4064771 / 1000000) (4163 / 100) (20857 / 500)
    (12711 / 125) (20621 / 200) (-568223 / 1000) (43949 / 250000) (545977 / 125) (325893 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4062609 / 1000000) (196383624249 / 1000000) (325893 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4062609 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4062609 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell209 :
    ∀ t ∈ Set.Icc ((2061 / 16000) : ℝ) (413 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((323463383 / 250000000) : ℝ) ≤ Real.exp (2 * (2061 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2061 / 16000)) (323463383 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((413 / 3200) : ℝ)) ≤ (647250311 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (413 / 3200)) (647250311 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((19758383897 / 100000) : ℝ) ≤ Real.exp (3 * (12702 / 3125)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (12702 / 3125)) (19758383897 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2061 / 16000) : ℝ) (413 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (12702 / 3125) (1016701 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2061 / 16000) (413 / 3200) (323463383 / 250000000) (647250311 / 500000000) (12702 / 3125) (1016701 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2061 / 16000) (413 / 3200) (12702 / 3125) (1016701 / 250000) (10421 / 250) (5221 / 125)
    (102027 / 1000) (103447 / 1000) (-71012 / 125) (17499 / 100000) (4376561 / 1000) (1295653 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (12702 / 3125) (19758383897 / 100000) (1295653 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (12702 / 3125)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (12702 / 3125)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell210 :
    ∀ t ∈ Set.Icc ((413 / 3200) : ℝ) (2069 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1294500621 / 1000000000) : ℝ) ≤ Real.exp (2 * (413 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (413 / 3200)) (1294500621 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2069 / 16000) : ℝ)) ≤ (647574017 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2069 / 16000)) (647574017 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((99396290809 / 500000) : ℝ) ≤ Real.exp (3 * (4066673 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4066673 / 1000000)) (99396290809 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((413 / 3200) : ℝ) (2069 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4066673 / 1000000) (2034419 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (413 / 3200) (2069 / 16000) (1294500621 / 1000000000) (647574017 / 500000000) (4066673 / 1000000) (2034419 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (413 / 3200) (2069 / 16000) (4066673 / 1000000) (2034419 / 500000) (20869 / 500) (20911 / 500)
    (12796 / 125) (10379 / 100) (-56797 / 100) (174187 / 1000000) (4385323 / 1000) (51511 / 40000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4066673 / 1000000) (99396290809 / 500000) (51511 / 40000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4066673 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4066673 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell211 :
    ∀ t ∈ Set.Icc ((2069 / 16000) : ℝ) (2073 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1295148033 / 1000000000) : ℝ) ≤ Real.exp (2 * (2069 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2069 / 16000)) (1295148033 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2073 / 16000) : ℝ)) ≤ (129579577 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2073 / 16000)) (129579577 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((40001863777 / 200000) : ℝ) ≤ Real.exp (3 * (4068707 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4068707 / 1000000)) (40001863777 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2069 / 16000) : ℝ) (2073 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4068707 / 1000000) (508859 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2069 / 16000) (2073 / 16000) (1295148033 / 1000000000) (129579577 / 100000000) (4068707 / 1000000) (508859 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2069 / 16000) (2073 / 16000) (4068707 / 1000000) (508859 / 125000) (5224 / 125) (10469 / 250)
    (102709 / 1000) (26033 / 250) (-70981 / 125) (173387 / 1000000) (4394099 / 1000) (1279941 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4068707 / 1000000) (40001863777 / 200000) (1279941 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4068707 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4068707 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell212 :
    ∀ t ∈ Set.Icc ((2073 / 16000) : ℝ) (2077 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1295795769 / 1000000000) : ℝ) ≤ Real.exp (2 * (2073 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2073 / 16000)) (1295795769 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2077 / 16000) : ℝ)) ≤ (129644383 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2077 / 16000)) (129644383 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8049364281 / 40000) : ℝ) ≤ Real.exp (3 * (2035371 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2035371 / 500000)) (8049364281 / 40000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2073 / 16000) : ℝ) (2077 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2035371 / 500000) (1018227 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2073 / 16000) (2077 / 16000) (1295795769 / 1000000000) (129644383 / 100000000) (2035371 / 500000) (1018227 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2073 / 16000) (2077 / 16000) (2035371 / 500000) (1018227 / 250000) (20923 / 500) (4193 / 100)
    (103051 / 1000) (26119 / 250) (-141929 / 250) (172591 / 1000000) (550362 / 125) (1272151 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2035371 / 500000) (8049364281 / 40000) (1272151 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2035371 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2035371 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell213 :
    ∀ t ∈ Set.Icc ((2077 / 16000) : ℝ) (2081 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1296443829 / 1000000000) : ℝ) ≤ Real.exp (2 * (2077 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2077 / 16000)) (1296443829 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2081 / 16000) : ℝ)) ≤ (648546107 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2081 / 16000)) (648546107 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((202467002709 / 1000000) : ℝ) ≤ Real.exp (3 * (2036389 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2036389 / 500000)) (202467002709 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2077 / 16000) : ℝ) (2081 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2036389 / 500000) (814989 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2077 / 16000) (2081 / 16000) (1296443829 / 1000000000) (648546107 / 500000000) (2036389 / 500000) (814989 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2077 / 16000) (2081 / 16000) (2036389 / 500000) (814989 / 200000) (419 / 10) (8397 / 200)
    (51697 / 500) (104821 / 1000) (-567581 / 1000) (171797 / 1000000) (4411711 / 1000) (316101 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2036389 / 500000) (202467002709 / 1000000) (316101 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2036389 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2036389 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell214 :
    ∀ t ∈ Set.Icc ((2081 / 16000) : ℝ) (417 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1297092213 / 1000000000) : ℝ) ≤ Real.exp (2 * (2081 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2081 / 16000)) (1297092213 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((417 / 3200) : ℝ)) ≤ (648870461 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (417 / 3200)) (648870461 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((203708063029 / 1000000) : ℝ) ≤ Real.exp (3 * (814963 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (814963 / 200000)) (203708063029 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2081 / 16000) : ℝ) (417 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (814963 / 200000) (4076983 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2081 / 16000) (417 / 3200) (1297092213 / 1000000000) (648870461 / 500000000) (814963 / 200000) (4076983 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2081 / 16000) (417 / 3200) (814963 / 200000) (4076983 / 1000000) (20977 / 500) (42039 / 1000)
    (51869 / 500) (52583 / 500) (-283721 / 500) (171007 / 1000000) (4420543 / 1000) (1256701 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (814963 / 200000) (203708063029 / 1000000) (1256701 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (814963 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (814963 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell215 :
    ∀ t ∈ Set.Icc ((417 / 3200) : ℝ) (2089 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1297740921 / 1000000000) : ℝ) ≤ Real.exp (2 * (417 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (417 / 3200)) (1297740921 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2089 / 16000) : ℝ)) ≤ (259677991 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2089 / 16000)) (259677991 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((409914691 / 2000) : ℝ) ≤ Real.exp (3 * (4076853 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4076853 / 1000000)) (409914691 / 2000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((417 / 3200) : ℝ) (2089 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4076853 / 1000000) (2039511 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (417 / 3200) (2089 / 16000) (1297740921 / 1000000000) (259677991 / 200000000) (4076853 / 1000000) (2039511 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (417 / 3200) (2089 / 16000) (4076853 / 1000000) (2039511 / 500000) (5251 / 125) (42093 / 1000)
    (52041 / 500) (13189 / 125) (-5673 / 10) (8511 / 50000) (4429393 / 1000) (1249041 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4076853 / 1000000) (409914691 / 2000) (1249041 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4076853 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4076853 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell216 :
    ∀ t ∈ Set.Icc ((2089 / 16000) : ℝ) (2093 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((649194977 / 500000000) : ℝ) ≤ Real.exp (2 * (2089 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2089 / 16000)) (649194977 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2093 / 16000) : ℝ)) ≤ (81189957 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2093 / 16000)) (81189957 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6444215877 / 31250) : ℝ) ≤ Real.exp (3 * (1019723 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1019723 / 250000)) (6444215877 / 31250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2089 / 16000) : ℝ) (2093 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1019723 / 250000) (2040531 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2089 / 16000) (2093 / 16000) (649194977 / 500000000) (81189957 / 62500000) (1019723 / 250000) (2040531 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2089 / 16000) (2093 / 16000) (1019723 / 250000) (2040531 / 500000) (42063 / 1000) (42147 / 1000)
    (104427 / 1000) (105859 / 1000) (-113431 / 200) (42359 / 250000) (4438261 / 1000) (77589 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1019723 / 250000) (6444215877 / 31250) (77589 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1019723 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1019723 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell217 :
    ∀ t ∈ Set.Icc ((2093 / 16000) : ℝ) (2097 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1299039311 / 1000000000) : ℝ) ≤ Real.exp (2 * (2093 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2093 / 16000)) (1299039311 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2097 / 16000) : ℝ)) ≤ (649844497 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2097 / 16000)) (649844497 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((103740093327 / 500000) : ℝ) ≤ Real.exp (3 * (4080931 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4080931 / 1000000)) (103740093327 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2093 / 16000) : ℝ) (2097 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4080931 / 1000000) (4083103 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2093 / 16000) (2097 / 16000) (1299039311 / 1000000000) (649844497 / 500000000) (4080931 / 1000000) (4083103 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2093 / 16000) (2097 / 16000) (4080931 / 1000000) (4083103 / 1000000) (42117 / 1000) (21101 / 500)
    (26193 / 250) (53103 / 500) (-567001 / 1000) (33731 / 200000) (2223573 / 500) (1233853 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4080931 / 1000000) (103740093327 / 500000) (1233853 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4080931 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4080931 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell218 :
    ∀ t ∈ Set.Icc ((2097 / 16000) : ℝ) (2101 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1299688993 / 1000000000) : ℝ) ≤ Real.exp (2 * (2097 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2097 / 16000)) (1299688993 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2101 / 16000) : ℝ)) ≤ (1300339001 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2101 / 16000)) (1300339001 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((20875448113 / 100000) : ℝ) ≤ Real.exp (3 * (1020743 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1020743 / 250000)) (20875448113 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2097 / 16000) : ℝ) (2101 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1020743 / 250000) (2042573 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2097 / 16000) (2101 / 16000) (1299688993 / 1000000000) (1300339001 / 1000000000) (1020743 / 250000) (2042573 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2097 / 16000) (2101 / 16000) (1020743 / 250000) (2042573 / 500000) (42171 / 1000) (5282 / 125)
    (52559 / 500) (21311 / 200) (-566843 / 1000) (167877 / 1000000) (4456053 / 1000) (1226321 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1020743 / 250000) (20875448113 / 100000) (1226321 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1020743 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1020743 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell219 :
    ∀ t ∈ Set.Icc ((2101 / 16000) : ℝ) (421 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1300339 / 1000000) : ℝ) ≤ Real.exp (2 * (2101 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2101 / 16000)) (1300339 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((421 / 3200) : ℝ)) ≤ (1300989333 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (421 / 3200)) (1300989333 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((42007446419 / 200000) : ℝ) ≤ Real.exp (3 * (2042507 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2042507 / 500000)) (42007446419 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2101 / 16000) : ℝ) (421 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2042507 / 500000) (4087189 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2101 / 16000) (421 / 3200) (1300339 / 1000000) (1300989333 / 1000000000) (2042507 / 500000) (4087189 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2101 / 16000) (421 / 3200) (2042507 / 500000) (4087189 / 1000000) (21113 / 500) (42311 / 1000)
    (21093 / 200) (13363 / 125) (-70836 / 125) (167103 / 1000000) (2232487 / 500) (76177 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2042507 / 500000) (42007446419 / 200000) (76177 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2042507 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2042507 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityExpCompact_cellsBatch010 :
    ∀ t ∈ Set.Icc ((81 / 640) : ℝ) (421 / 3200),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell200
      hpThetaDensityExpCompact_cell201)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell202
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell203
      hpThetaDensityExpCompact_cell204)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell205
      hpThetaDensityExpCompact_cell206)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell207
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell208
      hpThetaDensityExpCompact_cell209))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell210
      hpThetaDensityExpCompact_cell211)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell212
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell213
      hpThetaDensityExpCompact_cell214)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell215
      hpThetaDensityExpCompact_cell216)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell217
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell218
      hpThetaDensityExpCompact_cell219)))))

#print axioms hpThetaDensityExpCompact_cellsBatch010
end HodgeProofHP
