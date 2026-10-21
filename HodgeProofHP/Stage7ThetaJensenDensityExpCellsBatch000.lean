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
theorem hpThetaDensityExpCompact_cell000 :
    ∀ t ∈ Set.Icc ((1 / 10) : ℝ) (1601 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((610701379 / 500000000) : ℝ) ≤ Real.exp (2 * (1 / 10)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1 / 10)) (610701379 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1601 / 16000) : ℝ)) ≤ (305388861 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1601 / 16000)) (305388861 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((19963673253 / 200000) : ℝ) ≤ Real.exp (3 * (959259 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (959259 / 250000)) (19963673253 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1 / 10) : ℝ) (1601 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (959259 / 250000) (3837639 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1 / 10) (1601 / 16000) (610701379 / 500000000) (305388861 / 250000000) (959259 / 250000) (3837639 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1 / 10) (1601 / 16000) (959259 / 250000) (3837639 / 1000000) (7173 / 200) (4486 / 125)
    (16917 / 250) (6803 / 100) (-285297 / 500) (291063 / 1000000) (433797 / 125) (2564659 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (959259 / 250000) (19963673253 / 200000) (2564659 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (959259 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (959259 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell001 :
    ∀ t ∈ Set.Icc ((1601 / 16000) : ℝ) (801 / 8000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1221555443 / 1000000000) : ℝ) ≤ Real.exp (2 * (1601 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1601 / 16000)) (1221555443 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((801 / 8000) : ℝ)) ≤ (305427037 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (801 / 8000)) (305427037 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((24990552029 / 250000) : ℝ) ≤ Real.exp (3 * (959379 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (959379 / 250000)) (24990552029 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1601 / 16000) : ℝ) (801 / 8000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (959379 / 250000) (3838119 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1601 / 16000) (801 / 8000) (1221555443 / 1000000000) (305427037 / 250000000) (959379 / 250000) (3838119 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1601 / 16000) (801 / 8000) (959379 / 250000) (3838119 / 1000000) (35877 / 1000) (359 / 10)
    (33867 / 500) (8512 / 125) (-285321 / 500) (290753 / 1000000) (3472113 / 1000) (320121 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (959379 / 250000) (24990552029 / 250000) (320121 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (959379 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (959379 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell002 :
    ∀ t ∈ Set.Icc ((801 / 8000) : ℝ) (1603 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1221708147 / 1000000000) : ℝ) ≤ Real.exp (2 * (801 / 8000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (801 / 8000)) (1221708147 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1603 / 16000) : ℝ)) ≤ (1221860871 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1603 / 16000)) (1221860871 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3128320539 / 31250) : ℝ) ≤ Real.exp (3 * (959499 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (959499 / 250000)) (3128320539 / 31250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((801 / 8000) : ℝ) (1603 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (959499 / 250000) (3838599 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (801 / 8000) (1603 / 16000) (1221708147 / 1000000000) (1221860871 / 1000000000) (959499 / 250000) (3838599 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (801 / 8000) (1603 / 16000) (959499 / 250000) (3838599 / 1000000) (35889 / 1000) (4489 / 125)
    (339 / 5) (34081 / 500) (-57069 / 100) (290443 / 1000000) (69477 / 20) (2557283 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (959499 / 250000) (3128320539 / 31250) (2557283 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (959499 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (959499 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell003 :
    ∀ t ∈ Set.Icc ((1603 / 16000) : ℝ) (401 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((122186087 / 100000000) : ℝ) ≤ Real.exp (2 * (1603 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1603 / 16000)) (122186087 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((401 / 4000) : ℝ)) ≤ (1222013613 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (401 / 4000)) (1222013613 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((12531276651 / 125000) : ℝ) ≤ Real.exp (3 * (153539 / 40000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (153539 / 40000)) (12531276651 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1603 / 16000) : ℝ) (401 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (153539 / 40000) (1919539 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1603 / 16000) (401 / 4000) (122186087 / 100000000) (1222013613 / 1000000000) (153539 / 40000) (1919539 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1603 / 16000) (401 / 4000) (153539 / 40000) (1919539 / 500000) (35901 / 1000) (8981 / 250)
    (33933 / 500) (68229 / 1000) (-285369 / 500) (58027 / 200000) (434448 / 125) (2553611 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (153539 / 40000) (12531276651 / 125000) (2553611 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (153539 / 40000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (153539 / 40000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell004 :
    ∀ t ∈ Set.Icc ((401 / 4000) : ℝ) (321 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((305503403 / 250000000) : ℝ) ≤ Real.exp (2 * (401 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (401 / 4000)) (305503403 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((321 / 3200) : ℝ)) ≤ (611083187 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (321 / 3200)) (611083187 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((20078935473 / 200000) : ℝ) ≤ Real.exp (3 * (767791 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (767791 / 200000)) (20078935473 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((401 / 4000) : ℝ) (321 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (767791 / 200000) (1919779 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (401 / 4000) (321 / 3200) (305503403 / 250000000) (611083187 / 500000000) (767791 / 200000) (1919779 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (401 / 4000) (321 / 3200) (767791 / 200000) (1919779 / 500000) (4489 / 125) (4492 / 125)
    (67933 / 1000) (13659 / 200) (-285393 / 500) (144913 / 500000) (3477323 / 1000) (159371 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (767791 / 200000) (20078935473 / 200000) (159371 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (767791 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (767791 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell005 :
    ∀ t ∈ Set.Icc ((321 / 3200) : ℝ) (803 / 8000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1222166373 / 1000000000) : ℝ) ≤ Real.exp (2 * (321 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (321 / 3200)) (1222166373 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((803 / 8000) : ℝ)) ≤ (611159577 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (803 / 8000)) (611159577 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1005393497 / 10000) : ℝ) ≤ Real.exp (3 * (767887 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (767887 / 200000)) (1005393497 / 10000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((321 / 3200) : ℝ) (803 / 8000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (767887 / 200000) (1920019 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (321 / 3200) (803 / 8000) (1222166373 / 1000000000) (611159577 / 500000000) (767887 / 200000) (1920019 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (321 / 3200) (803 / 8000) (767887 / 200000) (1920019 / 500000) (8981 / 250) (35947 / 1000)
    (67999 / 1000) (34181 / 500) (-285417 / 500) (144759 / 500000) (1739531 / 500) (2546267 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (767887 / 200000) (1005393497 / 10000) (2546267 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (767887 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (767887 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell006 :
    ∀ t ∈ Set.Icc ((803 / 8000) : ℝ) (1607 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1222319153 / 1000000000) : ℝ) ≤ Real.exp (2 * (803 / 8000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (803 / 8000)) (1222319153 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1607 / 16000) : ℝ)) ≤ (611235977 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1607 / 16000)) (611235977 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6292764407 / 62500) : ℝ) ≤ Real.exp (3 * (767983 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (767983 / 200000)) (6292764407 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((803 / 8000) : ℝ) (1607 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (767983 / 200000) (1920259 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (803 / 8000) (1607 / 16000) (1222319153 / 1000000000) (611235977 / 500000000) (767983 / 200000) (1920259 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (803 / 8000) (1607 / 16000) (767983 / 200000) (1920259 / 500000) (4492 / 125) (35959 / 1000)
    (34033 / 500) (17107 / 250) (-570881 / 1000) (289209 / 1000000) (1740401 / 500) (2542603 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (767983 / 200000) (6292764407 / 62500) (2542603 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (767983 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (767983 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell007 :
    ∀ t ∈ Set.Icc ((1607 / 16000) : ℝ) (201 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1222471953 / 1000000000) : ℝ) ≤ Real.exp (2 * (1607 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1607 / 16000)) (1222471953 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((201 / 2000) : ℝ)) ≤ (305656193 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (201 / 2000)) (305656193 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((100829320103 / 1000000) : ℝ) ≤ Real.exp (3 * (768079 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (768079 / 200000)) (100829320103 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1607 / 16000) : ℝ) (201 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (768079 / 200000) (1920499 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1607 / 16000) (201 / 2000) (1222471953 / 1000000000) (305656193 / 250000000) (768079 / 200000) (1920499 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1607 / 16000) (201 / 2000) (768079 / 200000) (1920499 / 500000) (8987 / 250) (35971 / 1000)
    (17033 / 250) (13699 / 200) (-570929 / 1000) (144451 / 500000) (1741271 / 500) (507789 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (768079 / 200000) (100829320103 / 1000000) (507789 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (768079 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (768079 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell008 :
    ∀ t ∈ Set.Icc ((201 / 2000) : ℝ) (1609 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1222624771 / 1000000000) : ℝ) ≤ Real.exp (2 * (201 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (201 / 2000)) (1222624771 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1609 / 16000) : ℝ)) ≤ (122277761 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1609 / 16000)) (122277761 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((25243654693 / 250000) : ℝ) ≤ Real.exp (3 * (30727 / 8000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (30727 / 8000)) (25243654693 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((201 / 2000) : ℝ) (1609 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (30727 / 8000) (3841479 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (201 / 2000) (1609 / 16000) (1222624771 / 1000000000) (122277761 / 100000000) (30727 / 8000) (3841479 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (201 / 2000) (1609 / 16000) (30727 / 8000) (3841479 / 1000000) (899 / 25) (35983 / 1000)
    (34099 / 500) (34281 / 500) (-570971 / 1000) (144297 / 500000) (3484287 / 1000) (2535291 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (30727 / 8000) (25243654693 / 250000) (2535291 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (30727 / 8000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (30727 / 8000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell009 :
    ∀ t ∈ Set.Icc ((1609 / 16000) : ℝ) (161 / 1600), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1222777609 / 1000000000) : ℝ) ≤ Real.exp (2 * (1609 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1609 / 16000)) (1222777609 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((161 / 1600) : ℝ)) ≤ (1222930467 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (161 / 1600)) (1222930467 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((50560063411 / 500000) : ℝ) ≤ Real.exp (3 * (768271 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (768271 / 200000)) (50560063411 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1609 / 16000) : ℝ) (161 / 1600),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (768271 / 200000) (3841959 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1609 / 16000) (161 / 1600) (1222777609 / 1000000000) (1222930467 / 1000000000) (768271 / 200000) (3841959 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1609 / 16000) (161 / 1600) (768271 / 200000) (3841959 / 1000000) (8993 / 250) (7199 / 200)
    (13653 / 200) (17157 / 250) (-571019 / 1000) (288287 / 1000000) (3486029 / 1000) (2531643 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (768271 / 200000) (50560063411 / 500000) (2531643 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (768271 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (768271 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell010 :
    ∀ t ∈ Set.Icc ((161 / 1600) : ℝ) (1611 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((611465233 / 500000000) : ℝ) ≤ Real.exp (2 * (161 / 1600)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (161 / 1600)) (611465233 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1611 / 16000) : ℝ)) ≤ (1223083343 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1611 / 16000)) (1223083343 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((101266148351 / 1000000) : ℝ) ≤ Real.exp (3 * (960459 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (960459 / 250000)) (101266148351 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((161 / 1600) : ℝ) (1611 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (960459 / 250000) (3842439 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (161 / 1600) (1611 / 16000) (611465233 / 500000000) (1223083343 / 1000000000) (960459 / 250000) (3842439 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (161 / 1600) (1611 / 16000) (960459 / 250000) (3842439 / 1000000) (4498 / 125) (36007 / 1000)
    (17083 / 250) (34347 / 500) (-571071 / 1000) (287979 / 1000000) (3487771 / 1000) (315999 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (960459 / 250000) (101266148351 / 1000000) (315999 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (960459 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (960459 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell011 :
    ∀ t ∈ Set.Icc ((1611 / 16000) : ℝ) (403 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((611541671 / 500000000) : ℝ) ≤ Real.exp (2 * (1611 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1611 / 16000)) (611541671 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((403 / 4000) : ℝ)) ≤ (611618119 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (403 / 4000)) (611618119 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((20282415301 / 200000) : ℝ) ≤ Real.exp (3 * (960579 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (960579 / 250000)) (20282415301 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1611 / 16000) : ℝ) (403 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (960579 / 250000) (3842919 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1611 / 16000) (403 / 4000) (611541671 / 500000000) (611618119 / 500000000) (960579 / 250000) (3842919 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1611 / 16000) (403 / 4000) (960579 / 250000) (3842919 / 1000000) (8999 / 250) (36019 / 1000)
    (34199 / 500) (68761 / 1000) (-285559 / 500) (287673 / 1000000) (1744757 / 500) (504871 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (960579 / 250000) (20282415301 / 200000) (504871 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (960579 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (960579 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell012 :
    ∀ t ∈ Set.Icc ((403 / 4000) : ℝ) (1613 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1223236237 / 1000000000) : ℝ) ≤ Real.exp (2 * (403 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (403 / 4000)) (1223236237 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1613 / 16000) : ℝ)) ≤ (38230911 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1613 / 16000)) (38230911 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((50779107473 / 500000) : ℝ) ≤ Real.exp (3 * (960699 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (960699 / 250000)) (50779107473 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((403 / 4000) : ℝ) (1613 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (960699 / 250000) (19217 / 5000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (403 / 4000) (1613 / 16000) (1223236237 / 1000000000) (38230911 / 31250000) (960699 / 250000) (19217 / 5000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (403 / 4000) (1613 / 16000) (960699 / 250000) (19217 / 5000) (36007 / 1000) (36031 / 1000)
    (13693 / 200) (17207 / 250) (-571159 / 1000) (287367 / 1000000) (1745631 / 500) (1260361 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (960699 / 250000) (50779107473 / 500000) (1260361 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (960699 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (960699 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell013 :
    ∀ t ∈ Set.Icc ((1613 / 16000) : ℝ) (807 / 8000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1223389151 / 1000000000) : ℝ) ≤ Real.exp (2 * (1613 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1613 / 16000)) (1223389151 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((807 / 8000) : ℝ)) ≤ (244708417 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (807 / 8000)) (244708417 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((101704869091 / 1000000) : ℝ) ≤ Real.exp (3 * (3843277 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3843277 / 1000000)) (101704869091 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1613 / 16000) : ℝ) (807 / 8000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3843277 / 1000000) (96097 / 25000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1613 / 16000) (807 / 8000) (1223389151 / 1000000000) (244708417 / 200000000) (3843277 / 1000000) (96097 / 25000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1613 / 16000) (807 / 8000) (3843277 / 1000000) (96097 / 25000) (36019 / 1000) (18021 / 500)
    (17133 / 250) (13779 / 200) (-571211 / 1000) (14353 / 50000) (1746503 / 500) (2517087 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3843277 / 1000000) (101704869091 / 1000000) (2517087 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3843277 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3843277 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell014 :
    ∀ t ∈ Set.Icc ((807 / 8000) : ℝ) (323 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((305885521 / 250000000) : ℝ) ≤ Real.exp (2 * (807 / 8000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (807 / 8000)) (305885521 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((323 / 3200) : ℝ)) ≤ (1223695037 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (323 / 3200)) (1223695037 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6365714341 / 62500) : ℝ) ≤ Real.exp (3 * (3843757 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3843757 / 1000000)) (6365714341 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((807 / 8000) : ℝ) (323 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3843757 / 1000000) (3844361 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (807 / 8000) (323 / 3200) (305885521 / 250000000) (1223695037 / 1000000000) (3843757 / 1000000) (3844361 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (807 / 8000) (323 / 3200) (3843757 / 1000000) (3844361 / 1000000) (36031 / 1000) (18027 / 500)
    (34299 / 500) (34481 / 500) (-571253 / 1000) (143377 / 500000) (698951 / 200) (502693 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3843757 / 1000000) (6365714341 / 62500) (502693 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3843757 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3843757 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell015 :
    ∀ t ∈ Set.Icc ((323 / 3200) : ℝ) (101 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((305923759 / 250000000) : ℝ) ≤ Real.exp (2 * (323 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (323 / 3200)) (305923759 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((101 / 1000) : ℝ)) ≤ (1223848009 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (101 / 1000)) (1223848009 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((101998201019 / 1000000) : ℝ) ≤ Real.exp (3 * (3844237 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3844237 / 1000000)) (101998201019 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((323 / 3200) : ℝ) (101 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3844237 / 1000000) (3844841 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (323 / 3200) (101 / 1000) (305923759 / 250000000) (1223848009 / 1000000000) (3844237 / 1000000) (3844841 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (323 / 3200) (101 / 1000) (3844237 / 1000000) (3844841 / 1000000) (36043 / 1000) (18033 / 500)
    (13733 / 200) (69029 / 1000) (-571299 / 1000) (286449 / 1000000) (6993 / 2) (2509849 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3844237 / 1000000) (101998201019 / 1000000) (2509849 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3844237 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3844237 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell016 :
    ∀ t ∈ Set.Icc ((101 / 1000) : ℝ) (1617 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((152981001 / 125000000) : ℝ) ≤ Real.exp (2 * (101 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (101 / 1000)) (152981001 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1617 / 16000) : ℝ)) ≤ (1224000999 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1617 / 16000)) (1224000999 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((102145490521 / 1000000) : ℝ) ≤ Real.exp (3 * (1922359 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1922359 / 500000)) (102145490521 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((101 / 1000) : ℝ) (1617 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1922359 / 500000) (1922661 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (101 / 1000) (1617 / 16000) (152981001 / 125000000) (1224000999 / 1000000000) (1922359 / 500000) (1922661 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (101 / 1000) (1617 / 16000) (1922359 / 500000) (1922661 / 500000) (7211 / 200) (18039 / 500)
    (17183 / 250) (8637 / 125) (-285673 / 500) (286143 / 1000000) (13993 / 4) (250623 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1922359 / 500000) (102145490521 / 1000000) (250623 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1922359 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1922359 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell017 :
    ∀ t ∈ Set.Icc ((1617 / 16000) : ℝ) (809 / 8000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((612000499 / 500000000) : ℝ) ≤ Real.exp (2 * (1617 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1617 / 16000)) (612000499 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((809 / 8000) : ℝ)) ≤ (1224154009 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (809 / 8000)) (1224154009 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((51146496357 / 500000) : ℝ) ≤ Real.exp (3 * (3845199 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3845199 / 1000000)) (51146496357 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1617 / 16000) : ℝ) (809 / 8000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3845199 / 1000000) (3845803 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1617 / 16000) (809 / 8000) (612000499 / 500000000) (1224154009 / 1000000000) (3845199 / 1000000) (3845803 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1617 / 16000) (809 / 8000) (3845199 / 1000000) (3845803 / 1000000) (36067 / 1000) (3609 / 100)
    (68799 / 1000) (34581 / 500) (-71424 / 125) (142919 / 500000) (3500001 / 1000) (312827 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3845199 / 1000000) (51146496357 / 500000) (312827 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3845199 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3845199 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell018 :
    ∀ t ∈ Set.Icc ((809 / 8000) : ℝ) (1619 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((153019251 / 125000000) : ℝ) ≤ Real.exp (2 * (809 / 8000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (809 / 8000)) (153019251 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1619 / 16000) : ℝ)) ≤ (612153519 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1619 / 16000)) (612153519 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((20488080117 / 200000) : ℝ) ≤ Real.exp (3 * (3845679 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3845679 / 1000000)) (20488080117 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((809 / 8000) : ℝ) (1619 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3845679 / 1000000) (3846283 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (809 / 8000) (1619 / 16000) (153019251 / 125000000) (612153519 / 500000000) (3845679 / 1000000) (3846283 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (809 / 8000) (1619 / 16000) (3845679 / 1000000) (3846283 / 1000000) (36079 / 1000) (18051 / 500)
    (13773 / 200) (69229 / 1000) (-285719 / 500) (285533 / 1000000) (3501749 / 1000) (499803 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3845679 / 1000000) (20488080117 / 200000) (499803 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3845679 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3845679 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell019 :
    ∀ t ∈ Set.Icc ((1619 / 16000) : ℝ) (1621 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1224307037 / 1000000000) : ℝ) ≤ Real.exp (2 * (1619 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1619 / 16000)) (1224307037 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1621 / 16000) : ℝ)) ≤ (1224613153 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1621 / 16000)) (1224613153 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((102588328639 / 1000000) : ℝ) ≤ Real.exp (3 * (48077 / 12500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (48077 / 12500)) (102588328639 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1619 / 16000) : ℝ) (1621 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (48077 / 12500) (769449 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1619 / 16000) (1621 / 16000) (1224307037 / 1000000000) (1224613153 / 1000000000) (48077 / 12500) (769449 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1619 / 16000) (1621 / 16000) (48077 / 12500) (769449 / 200000) (4511 / 125) (36129 / 1000)
    (68821 / 1000) (34737 / 500) (-569121 / 1000) (35667 / 125000) (3505253 / 1000) (2495411 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (48077 / 12500) (102588328639 / 1000000) (2495411 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (48077 / 12500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (48077 / 12500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityExpCompact_cellsBatch000 :
    ∀ t ∈ Set.Icc ((1 / 10) : ℝ) (1621 / 16000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell000
      hpThetaDensityExpCompact_cell001)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell002
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell003
      hpThetaDensityExpCompact_cell004)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell005
      hpThetaDensityExpCompact_cell006)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell007
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell008
      hpThetaDensityExpCompact_cell009))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell010
      hpThetaDensityExpCompact_cell011)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell012
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell013
      hpThetaDensityExpCompact_cell014)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell015
      hpThetaDensityExpCompact_cell016)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell017
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell018
      hpThetaDensityExpCompact_cell019)))))

#print axioms hpThetaDensityExpCompact_cellsBatch000
end HodgeProofHP
