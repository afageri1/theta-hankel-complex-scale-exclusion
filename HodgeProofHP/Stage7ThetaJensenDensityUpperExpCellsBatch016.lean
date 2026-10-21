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
theorem hpThetaDensityUpperExpCompact_cell320 :
    ∀ t ∈ Set.Icc ((987 / 2000) : ℝ) (989 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((536634573 / 200000000) : ℝ) ≤ Real.exp (2 * (987 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (987 / 2000)) (536634573 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((989 / 2000) : ℝ)) ≤ (336068073 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (989 / 2000)) (336068073 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((42671479152557641 / 500000) : ℝ) ≤ Real.exp (3 * (8429187 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (8429187 / 1000000)) (42671479152557641 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((987 / 2000) : ℝ) (989 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (8429187 / 1000000) (2111583 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (987 / 2000) (989 / 2000) (536634573 / 200000000) (336068073 / 125000000) (8429187 / 1000000) (2111583 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (987 / 2000) (989 / 2000) (8429187 / 1000000) (2111583 / 250000) (116763 / 500) (234787 / 1000)
    (694363 / 250) (1407843 / 500) (12904697 / 500) (1 / 250000) (81431527 / 1000) (3 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (8429187 / 1000000) (42671479152557641 / 500000) (3 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8429187 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8429187 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell321 :
    ∀ t ∈ Set.Icc ((989 / 2000) : ℝ) (991 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2688544581 / 1000000000) : ℝ) ≤ Real.exp (2 * (989 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (989 / 2000)) (2688544581 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((991 / 2000) : ℝ)) ≤ (2693927053 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (991 / 2000)) (2693927053 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3582933641015257 / 40000) : ℝ) ≤ Real.exp (3 * (4223031 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4223031 / 500000)) (3582933641015257 / 40000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((989 / 2000) : ℝ) (991 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4223031 / 500000) (4231621 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (989 / 2000) (991 / 2000) (2688544581 / 1000000000) (2693927053 / 1000000000) (4223031 / 500000) (4231621 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (989 / 2000) (991 / 2000) (4223031 / 500000) (4231621 / 500000) (58641 / 250) (23583 / 100)
    (69949 / 25) (2836407 / 1000) (6526589 / 250) (1 / 250000) (82085609 / 1000) (3 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4223031 / 500000) (3582933641015257 / 40000) (3 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4223031 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4223031 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell322 :
    ∀ t ∈ Set.Icc ((991 / 2000) : ℝ) (993 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((53878541 / 20000000) : ℝ) ≤ Real.exp (2 * (991 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (991 / 2000)) (53878541 / 20000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((993 / 2000) : ℝ)) ≤ (2699320299 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (993 / 2000)) (2699320299 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((94019691595743573 / 1000000) : ℝ) ≤ Real.exp (3 * (8462971 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (8462971 / 1000000)) (94019691595743573 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((991 / 2000) : ℝ) (993 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (8462971 / 1000000) (1696037 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (991 / 2000) (993 / 2000) (53878541 / 20000000) (2699320299 / 1000000000) (8462971 / 1000000) (1696037 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (991 / 2000) (993 / 2000) (8462971 / 1000000) (1696037 / 200000) (117803 / 500) (236877 / 1000)
    (2818609 / 1000) (714317 / 250) (26406289 / 1000) (1 / 250000) (82744911 / 1000) (3 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (8462971 / 1000000) (94019691595743573 / 1000000) (3 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8462971 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8462971 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell323 :
    ∀ t ∈ Set.Icc ((993 / 2000) : ℝ) (199 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((337415037 / 125000000) : ℝ) ≤ Real.exp (2 * (993 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (993 / 2000)) (337415037 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((199 / 400) : ℝ)) ≤ (1352362171 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (199 / 400)) (1352362171 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((98693299606217161 / 1000000) : ℝ) ≤ Real.exp (3 * (4239957 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4239957 / 500000)) (98693299606217161 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((993 / 2000) : ℝ) (199 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4239957 / 500000) (4248581 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (993 / 2000) (199 / 400) (337415037 / 125000000) (1352362171 / 500000000) (4239957 / 500000) (4248581 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (993 / 2000) (199 / 400) (4239957 / 500000) (4248581 / 500000) (59163 / 250) (29741 / 125)
    (1419699 / 500) (287827 / 100) (13354631 / 500) (1 / 250000) (10426189 / 125) (3 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4239957 / 500000) (98693299606217161 / 1000000) (3 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4239957 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4239957 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell324 :
    ∀ t ∈ Set.Icc ((199 / 400) : ℝ) (997 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2704724339 / 1000000000) : ℝ) ≤ Real.exp (2 * (199 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (199 / 400)) (2704724339 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((997 / 2000) : ℝ)) ≤ (677534801 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (997 / 2000)) (677534801 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((51803028055867821 / 500000) : ℝ) ≤ Real.exp (3 * (8496891 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (8496891 / 1000000)) (51803028055867821 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((199 / 400) : ℝ) (997 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (8496891 / 1000000) (4257087 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (199 / 400) (997 / 2000) (2704724339 / 1000000000) (677534801 / 250000000) (8496891 / 1000000) (4257087 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (199 / 400) (997 / 2000) (8496891 / 1000000) (4257087 / 500000) (237703 / 1000) (29873 / 125)
    (2860329 / 1000) (2899417 / 1000) (5403069 / 200) (1 / 250000) (8407949 / 100) (3 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (8496891 / 1000000) (51803028055867821 / 500000) (3 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8496891 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8496891 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell325 :
    ∀ t ∈ Set.Icc ((997 / 2000) : ℝ) (999 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1693837 / 625000) : ℝ) ≤ Real.exp (2 * (997 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (997 / 2000)) (1693837 / 625000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((999 / 2000) : ℝ)) ≤ (1357782453 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (999 / 2000)) (1357782453 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((108770486162358487 / 1000000) : ℝ) ≤ Real.exp (3 * (4256951 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4256951 / 500000)) (108770486162358487 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((997 / 2000) : ℝ) (999 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4256951 / 500000) (8531219 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (997 / 2000) (999 / 2000) (1693837 / 625000) (1357782453 / 500000000) (4256951 / 500000) (8531219 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (997 / 2000) (999 / 2000) (4256951 / 500000) (8531219 / 1000000) (119379 / 500) (60011 / 250)
    (2881403 / 1000) (1460353 / 500) (683112 / 25) (1 / 250000) (84754809 / 1000) (3 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4256951 / 500000) (108770486162358487 / 1000000) (3 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4256951 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4256951 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell326 :
    ∀ t ∈ Set.Icc ((999 / 2000) : ℝ) (1 / 2), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2715564903 / 1000000000) : ℝ) ≤ Real.exp (2 * (999 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (999 / 2000)) (2715564903 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1 / 2) : ℝ)) ≤ (2718281829 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1 / 2)) (2718281829 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((7137486444603309 / 62500) : ℝ) ≤ Real.exp (3 * (8530947 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (8530947 / 1000000)) (7137486444603309 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((999 / 2000) : ℝ) (1 / 2),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (8530947 / 1000000) (1707951 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (999 / 2000) (1 / 2) (2715564903 / 1000000000) (2718281829 / 1000000000) (8530947 / 1000000) (1707951 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (999 / 2000) (1 / 2) (8530947 / 1000000) (1707951 / 200000) (239869 / 1000) (60131 / 250)
    (2906999 / 1000) (2927043 / 1000) (3408954 / 125) (1 / 250000) (85094527 / 1000) (3 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (8530947 / 1000000) (7137486444603309 / 62500) (3 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8530947 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8530947 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityUpperExpCompact_cellsBatch016 :
    ∀ t ∈ Set.Icc ((987 / 2000) : ℝ) (1 / 2),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell320
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell321
      hpThetaDensityUpperExpCompact_cell322))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell323
      hpThetaDensityUpperExpCompact_cell324)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell325
      hpThetaDensityUpperExpCompact_cell326)))

#print axioms hpThetaDensityUpperExpCompact_cellsBatch016
end HodgeProofHP
