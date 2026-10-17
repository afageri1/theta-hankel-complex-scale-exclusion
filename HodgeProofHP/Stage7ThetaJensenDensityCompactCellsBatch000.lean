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
theorem hpThetaDensityCompact_cell000 :
    ∀ t ∈ Set.Icc ((3 / 20) : ℝ) (601 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1349858807 / 1000000000) : ℝ) ≤ Real.exp (2 * (3 / 20)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3 / 20)) (1349858807 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((601 / 4000) : ℝ)) ≤ (675266953 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (601 / 4000)) (675266953 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((167475402979 / 500000) : ℝ) ≤ Real.exp (3 * (4240581 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4240581 / 1000000)) (167475402979 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3 / 20) : ℝ) (601 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4240581 / 1000000) (2121419 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (3 / 20) (601 / 4000) (1349858807 / 1000000000) (675266953 / 500000000) (4240581 / 1000000) (2121419 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (3 / 20) (601 / 4000) (4240581 / 1000000) (2121419 / 500000) (46473 / 1000) (11641 / 250)
    (133609 / 1000) (135193 / 1000) (-544493 / 1000) (489 / 200) (1036993 / 200) (191073 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4240581 / 1000000) (167475402979 / 500000) (191073 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4240581 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4240581 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell001 :
    ∀ t ∈ Set.Icc ((601 / 4000) : ℝ) (301 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((270106781 / 200000000) : ℝ) ≤ Real.exp (2 * (601 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (601 / 4000)) (270106781 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((301 / 2000) : ℝ)) ≤ (675604671 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (301 / 2000)) (675604671 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((168544439711 / 500000) : ℝ) ≤ Real.exp (3 * (2121351 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2121351 / 500000)) (168544439711 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((601 / 4000) : ℝ) (301 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2121351 / 500000) (26531 / 6250) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (601 / 4000) (301 / 2000) (270106781 / 200000000) (675604671 / 500000000) (2121351 / 500000) (26531 / 6250) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (601 / 4000) (301 / 2000) (2121351 / 500000) (26531 / 6250) (11633 / 250) (46623 / 1000)
    (16752 / 125) (67801 / 500) (-272021 / 500) (306 / 125) (1039069 / 200) (189861 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2121351 / 500000) (168544439711 / 500000) (189861 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2121351 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2121351 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell002 :
    ∀ t ∈ Set.Icc ((301 / 2000) : ℝ) (603 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1351209341 / 1000000000) : ℝ) ≤ Real.exp (2 * (301 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (301 / 2000)) (1351209341 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((603 / 4000) : ℝ)) ≤ (337971279 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (603 / 4000)) (337971279 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((169620809163 / 500000) : ℝ) ≤ Real.exp (3 * (530603 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (530603 / 125000)) (169620809163 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((301 / 2000) : ℝ) (603 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (530603 / 125000) (4247083 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (301 / 2000) (603 / 4000) (1351209341 / 1000000000) (337971279 / 250000000) (530603 / 125000) (4247083 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (301 / 2000) (603 / 4000) (530603 / 125000) (4247083 / 1000000) (46591 / 1000) (23341 / 500)
    (16803 / 125) (34003 / 250) (-543587 / 1000) (613 / 250) (5205747 / 1000) (6037 / 8000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (530603 / 125000) (169620809163 / 500000) (6037 / 8000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (530603 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (530603 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell003 :
    ∀ t ∈ Set.Icc ((603 / 4000) : ℝ) (151 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((270377023 / 200000000) : ℝ) ≤ Real.exp (2 * (603 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (603 / 4000)) (270377023 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((151 / 1000) : ℝ)) ≤ (1352561227 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (151 / 1000)) (1352561227 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((170704564641 / 500000) : ℝ) ≤ Real.exp (3 * (4246947 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4246947 / 1000000)) (170704564641 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((603 / 4000) : ℝ) (151 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4246947 / 1000000) (4249207 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (603 / 4000) (151 / 1000) (270377023 / 200000000) (1352561227 / 1000000000) (4246947 / 1000000) (4249207 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (603 / 4000) (151 / 1000) (4246947 / 1000000) (4249207 / 1000000) (933 / 20) (23371 / 500)
    (134833 / 1000) (136423 / 1000) (-543127 / 1000) (307 / 125) (652021 / 125) (374917 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4246947 / 1000000) (170704564641 / 500000) (374917 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4246947 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4246947 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell004 :
    ∀ t ∈ Set.Icc ((151 / 1000) : ℝ) (121 / 800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((676280613 / 500000000) : ℝ) ≤ Real.exp (2 * (151 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (151 / 1000)) (676280613 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((121 / 800) : ℝ)) ≤ (1353237677 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (121 / 800)) (1353237677 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((343591519717 / 1000000) : ℝ) ≤ Real.exp (3 * (4249071 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4249071 / 1000000)) (343591519717 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((151 / 1000) : ℝ) (121 / 800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4249071 / 1000000) (1062833 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (151 / 1000) (121 / 800) (676280613 / 500000000) (1353237677 / 1000000000) (4249071 / 1000000) (1062833 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (151 / 1000) (121 / 800) (4249071 / 1000000) (1062833 / 250000) (4671 / 100) (46801 / 1000)
    (135243 / 1000) (27367 / 200) (-271331 / 500) (2459 / 1000) (522661 / 100) (745071 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4249071 / 1000000) (343591519717 / 1000000) (745071 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4249071 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4249071 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell005 :
    ∀ t ∈ Set.Icc ((121 / 800) : ℝ) (303 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((338309419 / 250000000) : ℝ) ≤ Real.exp (2 * (121 / 800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (121 / 800)) (338309419 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((303 / 2000) : ℝ)) ≤ (270782893 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (303 / 2000)) (270782893 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((345788897879 / 1000000) : ℝ) ≤ Real.exp (3 * (1062799 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1062799 / 250000)) (345788897879 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((121 / 800) : ℝ) (303 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1062799 / 250000) (2126729 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (121 / 800) (303 / 2000) (338309419 / 250000000) (270782893 / 200000000) (1062799 / 250000) (2126729 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (121 / 800) (303 / 2000) (1062799 / 250000) (2126729 / 500000) (46769 / 1000) (46861 / 1000)
    (67827 / 500) (17156 / 125) (-542193 / 1000) (2463 / 1000) (5237073 / 1000) (740337 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1062799 / 250000) (345788897879 / 1000000) (740337 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1062799 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1062799 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell006 :
    ∀ t ∈ Set.Icc ((303 / 2000) : ℝ) (607 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((42309827 / 31250000) : ℝ) ≤ Real.exp (2 * (303 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (303 / 2000)) (42309827 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((607 / 4000) : ℝ)) ≤ (1354591591 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (607 / 4000)) (1354591591 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((348001372841 / 1000000) : ℝ) ≤ Real.exp (3 * (2126661 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2126661 / 500000)) (348001372841 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((303 / 2000) : ℝ) (607 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2126661 / 500000) (851117 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (303 / 2000) (607 / 4000) (42309827 / 31250000) (1354591591 / 1000000000) (2126661 / 500000) (851117 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (303 / 2000) (607 / 4000) (2126661 / 500000) (851117 / 200000) (46829 / 1000) (46921 / 1000)
    (27213 / 200) (137661 / 1000) (-13543 / 25) (2467 / 1000) (1311889 / 250) (73563 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2126661 / 500000) (348001372841 / 1000000) (73563 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2126661 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2126661 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell007 :
    ∀ t ∈ Set.Icc ((607 / 4000) : ℝ) (19 / 125), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((135459159 / 100000000) : ℝ) ≤ Real.exp (2 * (607 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (607 / 4000)) (135459159 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((19 / 125) : ℝ)) ≤ (1355269057 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (19 / 125)) (1355269057 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((175114527257 / 500000) : ℝ) ≤ Real.exp (3 * (4255449 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4255449 / 1000000)) (175114527257 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((607 / 4000) : ℝ) (19 / 125),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4255449 / 1000000) (2128857 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (607 / 4000) (19 / 125) (135459159 / 100000000) (1355269057 / 1000000000) (4255449 / 1000000) (2128857 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (607 / 4000) (19 / 125) (4255449 / 1000000) (2128857 / 500000) (46889 / 1000) (2349 / 50)
    (68239 / 500) (34519 / 250) (-108247 / 200) (247 / 100) (1051613 / 200) (730951 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4255449 / 1000000) (175114527257 / 500000) (730951 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4255449 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4255449 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell008 :
    ∀ t ∈ Set.Icc ((19 / 125) : ℝ) (609 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((21176079 / 15625000) : ℝ) ≤ Real.exp (2 * (19 / 125)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (19 / 125)) (21176079 / 15625000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((609 / 4000) : ℝ)) ≤ (1355946861 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (609 / 4000)) (1355946861 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((70494410729 / 200000) : ℝ) ≤ Real.exp (3 * (4257577 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4257577 / 1000000)) (70494410729 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((19 / 125) : ℝ) (609 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4257577 / 1000000) (4259843 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (19 / 125) (609 / 4000) (21176079 / 15625000) (1355946861 / 1000000000) (4257577 / 1000000) (4259843 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (19 / 125) (609 / 4000) (4257577 / 1000000) (4259843 / 1000000) (11737 / 250) (1176 / 25)
    (136891 / 1000) (138491 / 1000) (-540753 / 1000) (1237 / 500) (526859 / 100) (726299 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4257577 / 1000000) (70494410729 / 200000) (726299 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4257577 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4257577 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell009 :
    ∀ t ∈ Set.Icc ((609 / 4000) : ℝ) (61 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((67797343 / 50000000) : ℝ) ≤ Real.exp (2 * (609 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (609 / 4000)) (67797343 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((61 / 400) : ℝ)) ≤ (339156251 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (61 / 400)) (339156251 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((177365773009 / 500000) : ℝ) ≤ Real.exp (3 * (4259707 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4259707 / 1000000)) (177365773009 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((609 / 4000) : ℝ) (61 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4259707 / 1000000) (2130987 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (609 / 4000) (61 / 400) (67797343 / 50000000) (339156251 / 250000000) (4259707 / 1000000) (2130987 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (609 / 4000) (61 / 400) (4259707 / 1000000) (2130987 / 500000) (5876 / 125) (471 / 10)
    (27461 / 200) (138907 / 1000) (-108053 / 200) (1239 / 500) (263957 / 50) (721673 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4259707 / 1000000) (177365773009 / 500000) (721673 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4259707 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4259707 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell010 :
    ∀ t ∈ Set.Icc ((61 / 400) : ℝ) (611 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1356625003 / 1000000000) : ℝ) ≤ Real.exp (2 * (61 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (61 / 400)) (1356625003 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((611 / 4000) : ℝ)) ≤ (678651743 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (611 / 4000)) (678651743 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((357005522533 / 1000000) : ℝ) ≤ Real.exp (3 * (4261837 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4261837 / 1000000)) (357005522533 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((61 / 400) : ℝ) (611 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4261837 / 1000000) (852821 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (61 / 400) (611 / 4000) (1356625003 / 1000000000) (678651743 / 500000000) (4261837 / 1000000) (852821 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (61 / 400) (611 / 4000) (4261837 / 1000000) (852821 / 200000) (11767 / 250) (1179 / 25)
    (3443 / 25) (34831 / 250) (-269887 / 500) (1241 / 500) (5289707 / 1000) (179269 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4261837 / 1000000) (357005522533 / 1000000) (179269 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4261837 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4261837 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell011 :
    ∀ t ∈ Set.Icc ((611 / 4000) : ℝ) (153 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((271460697 / 200000000) : ℝ) ≤ Real.exp (2 * (611 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (611 / 4000)) (271460697 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((153 / 1000) : ℝ)) ≤ (1357982307 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (153 / 1000)) (1357982307 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((179647576957 / 500000) : ℝ) ≤ Real.exp (3 * (133249 / 31250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (133249 / 31250)) (179647576957 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((611 / 4000) : ℝ) (153 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (133249 / 31250) (2133119 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (611 / 4000) (153 / 1000) (271460697 / 200000000) (1357982307 / 1000000000) (133249 / 31250) (2133119 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (611 / 4000) (153 / 1000) (133249 / 31250) (2133119 / 500000) (5891 / 125) (2361 / 50)
    (27627 / 200) (69871 / 500) (-539271 / 1000) (497 / 200) (5300299 / 1000) (712507 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (133249 / 31250) (179647576957 / 500000) (712507 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (133249 / 31250)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (133249 / 31250)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell012 :
    ∀ t ∈ Set.Icc ((153 / 1000) : ℝ) (613 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((678991153 / 500000000) : ℝ) ≤ Real.exp (2 * (153 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (153 / 1000)) (678991153 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((613 / 4000) : ℝ)) ≤ (339665367 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (613 / 4000)) (339665367 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((72320327827 / 200000) : ℝ) ≤ Real.exp (3 * (4266101 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4266101 / 1000000)) (72320327827 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((153 / 1000) : ℝ) (613 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4266101 / 1000000) (4268371 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (153 / 1000) (613 / 4000) (678991153 / 500000000) (339665367 / 250000000) (4266101 / 1000000) (4268371 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (153 / 1000) (613 / 4000) (4266101 / 1000000) (4268371 / 1000000) (11797 / 250) (1182 / 25)
    (138553 / 1000) (140161 / 1000) (-67347 / 125) (2489 / 1000) (5310907 / 1000) (353981 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4266101 / 1000000) (72320327827 / 200000) (353981 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4266101 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4266101 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell013 :
    ∀ t ∈ Set.Icc ((613 / 4000) : ℝ) (307 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1358661467 / 1000000000) : ℝ) ≤ Real.exp (2 * (613 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (613 / 4000)) (1358661467 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((307 / 2000) : ℝ)) ≤ (1359340969 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (307 / 2000)) (1359340969 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((582276689 / 1600) : ℝ) ≤ Real.exp (3 * (2134117 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2134117 / 500000)) (582276689 / 1600) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((613 / 4000) : ℝ) (307 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2134117 / 500000) (2135253 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (613 / 4000) (307 / 2000) (1358661467 / 1000000000) (1359340969 / 1000000000) (2134117 / 500000) (2135253 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (613 / 4000) (307 / 2000) (2134117 / 500000) (2135253 / 500000) (5906 / 125) (2367 / 50)
    (13897 / 100) (140581 / 1000) (-67283 / 125) (2493 / 1000) (266077 / 50) (351723 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2134117 / 500000) (582276689 / 1600) (351723 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2134117 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2134117 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell014 :
    ∀ t ∈ Set.Icc ((307 / 2000) : ℝ) (123 / 800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((169917621 / 125000000) : ℝ) ≤ Real.exp (2 * (307 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (307 / 2000)) (169917621 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((123 / 800) : ℝ)) ≤ (1360020809 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (123 / 800)) (1360020809 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((366261320973 / 1000000) : ℝ) ≤ Real.exp (3 * (4270369 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4270369 / 1000000)) (366261320973 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((307 / 2000) : ℝ) (123 / 800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4270369 / 1000000) (2136321 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (307 / 2000) (123 / 800) (169917621 / 125000000) (1360020809 / 1000000000) (4270369 / 1000000) (2136321 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (307 / 2000) (123 / 800) (4270369 / 1000000) (2136321 / 500000) (11827 / 250) (237 / 5)
    (34847 / 250) (141001 / 1000) (-268877 / 500) (312 / 125) (1066439 / 200) (139791 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4270369 / 1000000) (366261320973 / 1000000) (139791 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4270369 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4270369 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell015 :
    ∀ t ∈ Set.Icc ((123 / 800) : ℝ) (77 / 500), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((170002601 / 125000000) : ℝ) ≤ Real.exp (2 * (123 / 800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (123 / 800)) (170002601 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((77 / 500) : ℝ)) ≤ (1360700989 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (77 / 500)) (1360700989 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((73723168471 / 200000) : ℝ) ≤ Real.exp (3 * (854501 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (854501 / 200000)) (73723168471 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((123 / 800) : ℝ) (77 / 500),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (854501 / 200000) (4274779 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (123 / 800) (77 / 500) (170002601 / 125000000) (1360700989 / 1000000000) (854501 / 200000) (4274779 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (123 / 800) (77 / 500) (854501 / 200000) (4274779 / 1000000) (5921 / 125) (2373 / 50)
    (17476 / 125) (141423 / 1000) (-537239 / 1000) (5 / 2) (5342871 / 1000) (69449 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (854501 / 200000) (73723168471 / 200000) (69449 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (854501 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (854501 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell016 :
    ∀ t ∈ Set.Icc ((77 / 500) : ℝ) (617 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((340175247 / 250000000) : ℝ) ≤ Real.exp (2 * (77 / 500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (77 / 500)) (340175247 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((617 / 4000) : ℝ)) ≤ (136138151 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (617 / 4000)) (136138151 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((370986612639 / 1000000) : ℝ) ≤ Real.exp (3 * (2137321 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2137321 / 500000)) (370986612639 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((77 / 500) : ℝ) (617 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2137321 / 500000) (4276917 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (77 / 500) (617 / 4000) (340175247 / 250000000) (136138151 / 100000000) (2137321 / 500000) (4276917 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (77 / 500) (617 / 4000) (2137321 / 500000) (4276917 / 1000000) (11857 / 250) (47521 / 1000)
    (35057 / 250) (28369 / 200) (-536719 / 1000) (313 / 125) (669196 / 125) (172513 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2137321 / 500000) (370986612639 / 1000000) (172513 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2137321 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2137321 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell017 :
    ∀ t ∈ Set.Icc ((617 / 4000) : ℝ) (309 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1361381509 / 1000000000) : ℝ) ≤ Real.exp (2 * (617 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (617 / 4000)) (1361381509 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((309 / 2000) : ℝ)) ≤ (1362062371 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (309 / 2000)) (1362062371 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((93343437649 / 250000) : ℝ) ≤ Real.exp (3 * (213839 / 50000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (213839 / 50000)) (93343437649 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((617 / 4000) : ℝ) (309 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (213839 / 50000) (267441 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (617 / 4000) (309 / 2000) (1361381509 / 1000000000) (1362062371 / 1000000000) (213839 / 50000) (267441 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (617 / 4000) (309 / 2000) (213839 / 50000) (267441 / 62500) (47489 / 1000) (47581 / 1000)
    (140649 / 1000) (35567 / 250) (-107239 / 200) (627 / 250) (2682143 / 500) (685641 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (213839 / 50000) (93343437649 / 250000) (685641 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (213839 / 50000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (213839 / 50000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell018 :
    ∀ t ∈ Set.Icc ((309 / 2000) : ℝ) (619 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((136206237 / 100000000) : ℝ) ≤ Real.exp (2 * (309 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (309 / 2000)) (136206237 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((619 / 4000) : ℝ)) ≤ (340685893 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (619 / 4000)) (340685893 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((375776248589 / 1000000) : ℝ) ≤ Real.exp (3 * (2139459 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2139459 / 500000)) (375776248589 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((309 / 2000) : ℝ) (619 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2139459 / 500000) (1070299 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (309 / 2000) (619 / 4000) (136206237 / 100000000) (340685893 / 250000000) (2139459 / 500000) (1070299 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (309 / 2000) (619 / 4000) (2139459 / 500000) (1070299 / 250000) (47549 / 1000) (23821 / 500)
    (141071 / 1000) (35673 / 250) (-535659 / 1000) (2511 / 1000) (215001 / 40) (681257 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2139459 / 500000) (375776248589 / 1000000) (681257 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2139459 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2139459 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell019 :
    ∀ t ∈ Set.Icc ((619 / 4000) : ℝ) (31 / 200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1362743571 / 1000000000) : ℝ) ≤ Real.exp (2 * (619 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (619 / 4000)) (1362743571 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((31 / 200) : ℝ)) ≤ (272685023 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (31 / 200)) (272685023 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((75639294921 / 200000) : ℝ) ≤ Real.exp (3 * (2140529 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2140529 / 500000)) (75639294921 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((619 / 4000) : ℝ) (31 / 200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2140529 / 500000) (4283337 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (619 / 4000) (31 / 200) (1362743571 / 1000000000) (272685023 / 200000000) (2140529 / 500000) (4283337 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (619 / 4000) (31 / 200) (2140529 / 500000) (4283337 / 1000000) (47609 / 1000) (23851 / 500)
    (141493 / 1000) (143117 / 1000) (-267563 / 500) (503 / 200) (1077157 / 200) (676897 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2140529 / 500000) (75639294921 / 200000) (676897 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2140529 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2140529 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityCompact_cellsBatch000 :
    ∀ t ∈ Set.Icc ((3 / 20) : ℝ) (31 / 200),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell000
      hpThetaDensityCompact_cell001)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell002
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell003
      hpThetaDensityCompact_cell004)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell005
      hpThetaDensityCompact_cell006)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell007
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell008
      hpThetaDensityCompact_cell009))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell010
      hpThetaDensityCompact_cell011)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell012
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell013
      hpThetaDensityCompact_cell014)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell015
      hpThetaDensityCompact_cell016)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell017
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell018
      hpThetaDensityCompact_cell019)))))

#print axioms hpThetaDensityCompact_cellsBatch000
end HodgeProofHP
