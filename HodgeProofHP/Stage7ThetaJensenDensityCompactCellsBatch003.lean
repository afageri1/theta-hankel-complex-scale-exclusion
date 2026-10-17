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
theorem hpThetaDensityCompact_cell060 :
    ∀ t ∈ Set.Icc ((33 / 200) : ℝ) (661 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((21733877 / 15625000) : ℝ) ≤ Real.exp (2 * (33 / 200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (33 / 200)) (21733877 / 15625000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((661 / 4000) : ℝ)) ≤ (1391663787 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (661 / 4000)) (1391663787 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((493446978167 / 1000000) : ℝ) ≤ Real.exp (3 * (2184863 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2184863 / 500000)) (493446978167 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((33 / 200) : ℝ) (661 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2184863 / 500000) (4372051 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (33 / 200) (661 / 4000) (21733877 / 15625000) (1391663787 / 1000000000) (2184863 / 500000) (4372051 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (33 / 200) (661 / 4000) (2184863 / 500000) (4372051 / 1000000) (10029 / 200) (50241 / 1000)
    (159603 / 1000) (80657 / 500) (-254459 / 500) (107 / 40) (1461507 / 250) (1297 / 2500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2184863 / 500000) (493446978167 / 1000000) (1297 / 2500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2184863 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2184863 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell061 :
    ∀ t ∈ Set.Icc ((661 / 4000) : ℝ) (331 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((695831893 / 500000000) : ℝ) ≤ Real.exp (2 * (661 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (661 / 4000)) (695831893 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((331 / 2000) : ℝ)) ≤ (1392359793 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (331 / 2000)) (1392359793 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((248346055977 / 500000) : ℝ) ≤ Real.exp (3 * (4371911 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4371911 / 1000000)) (248346055977 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((661 / 4000) : ℝ) (331 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4371911 / 1000000) (2187119 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (661 / 4000) (331 / 2000) (695831893 / 500000000) (1392359793 / 1000000000) (4371911 / 1000000) (2187119 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (661 / 4000) (331 / 2000) (4371911 / 1000000) (2187119 / 500000) (6276 / 125) (10061 / 200)
    (160063 / 1000) (80889 / 500) (-127041 / 250) (2679 / 1000) (2928867 / 500) (51541 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4371911 / 1000000) (248346055977 / 500000) (51541 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4371911 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4371911 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell062 :
    ∀ t ∈ Set.Icc ((331 / 2000) : ℝ) (663 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((87022487 / 62500000) : ℝ) ≤ Real.exp (2 * (331 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (331 / 2000)) (87022487 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((663 / 4000) : ℝ)) ≤ (1393056147 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (663 / 4000)) (1393056147 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((124990396659 / 250000) : ℝ) ≤ Real.exp (3 * (2187049 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2187049 / 500000)) (124990396659 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((331 / 2000) : ℝ) (663 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2187049 / 500000) (2188213 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (331 / 2000) (663 / 4000) (87022487 / 62500000) (1393056147 / 1000000000) (2187049 / 500000) (2188213 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (331 / 2000) (663 / 4000) (2187049 / 500000) (2188213 / 500000) (6284 / 125) (6296 / 125)
    (6421 / 40) (81121 / 500) (-50741 / 100) (2683 / 1000) (5869463 / 1000) (12801 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2187049 / 500000) (124990396659 / 250000) (12801 / 25000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2187049 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2187049 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell063 :
    ∀ t ∈ Set.Icc ((663 / 4000) : ℝ) (83 / 500), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((696528073 / 500000000) : ℝ) ≤ Real.exp (2 * (663 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (663 / 4000)) (696528073 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((83 / 500) : ℝ)) ≤ (1393752849 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (83 / 500)) (1393752849 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((5032525823 / 10000) : ℝ) ≤ Real.exp (3 * (875257 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (875257 / 200000)) (5032525823 / 10000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((663 / 4000) : ℝ) (83 / 500),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (875257 / 200000) (2189307 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (663 / 4000) (83 / 500) (696528073 / 500000000) (1393752849 / 1000000000) (875257 / 200000) (2189307 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (663 / 4000) (83 / 500) (875257 / 200000) (2189307 / 500000) (10067 / 200) (6304 / 125)
    (40247 / 250) (162707 / 1000) (-506651 / 1000) (2687 / 1000) (588121 / 100) (508691 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (875257 / 200000) (5032525823 / 10000) (508691 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (875257 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (875257 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell064 :
    ∀ t ∈ Set.Icc ((83 / 500) : ℝ) (133 / 800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((87109553 / 62500000) : ℝ) ≤ Real.exp (2 * (83 / 500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (83 / 500)) (87109553 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((133 / 800) : ℝ)) ≤ (13944499 / 10000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (133 / 800)) (13944499 / 10000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((15830258749 / 31250) : ℝ) ≤ Real.exp (3 * (2189237 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2189237 / 500000)) (15830258749 / 31250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((83 / 500) : ℝ) (133 / 800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2189237 / 500000) (1095201 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (83 / 500) (133 / 800) (87109553 / 62500000) (13944499 / 10000000) (2189237 / 500000) (1095201 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (83 / 500) (133 / 800) (2189237 / 500000) (1095201 / 250000) (50399 / 1000) (10099 / 200)
    (40363 / 250) (163173 / 1000) (-252943 / 500) (2691 / 1000) (1178597 / 200) (252681 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2189237 / 500000) (15830258749 / 31250) (252681 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2189237 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2189237 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell065 :
    ∀ t ∈ Set.Icc ((133 / 800) : ℝ) (333 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1394449899 / 1000000000) : ℝ) ≤ Real.exp (2 * (133 / 800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (133 / 800)) (1394449899 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((333 / 2000) : ℝ)) ≤ (1395147299 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (333 / 2000)) (1395147299 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((254953676297 / 500000) : ℝ) ≤ Real.exp (3 * (547583 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (547583 / 125000)) (254953676297 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((133 / 800) : ℝ) (333 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (547583 / 125000) (876599 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (133 / 800) (333 / 2000) (1394449899 / 1000000000) (1395147299 / 1000000000) (547583 / 125000) (876599 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (133 / 800) (333 / 2000) (547583 / 125000) (876599 / 200000) (25231 / 500) (50559 / 1000)
    (161917 / 1000) (4091 / 25) (-126279 / 250) (539 / 200) (5904783 / 1000) (125513 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (547583 / 125000) (254953676297 / 500000) (125513 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (547583 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (547583 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell066 :
    ∀ t ∈ Set.Icc ((333 / 2000) : ℝ) (667 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((697573649 / 500000000) : ℝ) ≤ Real.exp (2 * (333 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (333 / 2000)) (697573649 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((667 / 4000) : ℝ)) ≤ (1395845047 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (667 / 4000)) (1395845047 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((128317493587 / 250000) : ℝ) ≤ Real.exp (3 * (876571 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (876571 / 200000)) (128317493587 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((333 / 2000) : ℝ) (667 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (876571 / 200000) (4385187 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (333 / 2000) (667 / 4000) (697573649 / 500000000) (1395845047 / 1000000000) (876571 / 200000) (4385187 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (333 / 2000) (667 / 4000) (876571 / 200000) (4385187 / 1000000) (25263 / 500) (50623 / 1000)
    (162383 / 1000) (41027 / 250) (-25217 / 50) (2699 / 1000) (1479151 / 250) (498763 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (876571 / 200000) (128317493587 / 250000) (498763 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (876571 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (876571 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell067 :
    ∀ t ∈ Set.Icc ((667 / 4000) : ℝ) (167 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((697922523 / 500000000) : ℝ) ≤ Real.exp (2 * (667 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (667 / 4000)) (697922523 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((167 / 1000) : ℝ)) ≤ (174567893 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (167 / 1000)) (174567893 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((516656320761 / 1000000) : ℝ) ≤ Real.exp (3 * (4385047 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4385047 / 1000000)) (516656320761 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((667 / 4000) : ℝ) (167 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4385047 / 1000000) (219369 / 50000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (667 / 4000) (167 / 1000) (697922523 / 500000000) (174567893 / 125000000) (4385047 / 1000000) (219369 / 50000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (667 / 4000) (167 / 1000) (4385047 / 1000000) (219369 / 50000) (5059 / 100) (50687 / 1000)
    (3257 / 20) (164577 / 1000) (-503559 / 1000) (2703 / 1000) (741056 / 125) (247747 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4385047 / 1000000) (516656320761 / 1000000) (247747 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4385047 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4385047 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell068 :
    ∀ t ∈ Set.Icc ((167 / 1000) : ℝ) (669 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1396543143 / 1000000000) : ℝ) ≤ Real.exp (2 * (167 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (167 / 1000)) (1396543143 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((669 / 4000) : ℝ)) ≤ (139724159 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (669 / 4000)) (139724159 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((104013313747 / 200000) : ℝ) ≤ Real.exp (3 * (109681 / 25000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (109681 / 25000)) (104013313747 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((167 / 1000) : ℝ) (669 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (109681 / 25000) (175583 / 40000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (167 / 1000) (669 / 4000) (1396543143 / 1000000000) (139724159 / 100000000) (109681 / 25000) (175583 / 40000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (167 / 1000) (669 / 4000) (109681 / 25000) (175583 / 40000) (25327 / 500) (50751 / 1000)
    (163317 / 1000) (165047 / 1000) (-100553 / 200) (2707 / 1000) (5940321 / 1000) (98449 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (109681 / 25000) (104013313747 / 200000) (98449 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (109681 / 25000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (109681 / 25000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell069 :
    ∀ t ∈ Set.Icc ((669 / 4000) : ℝ) (67 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1397241589 / 1000000000) : ℝ) ≤ Real.exp (2 * (669 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (669 / 4000)) (1397241589 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((67 / 400) : ℝ)) ≤ (698970193 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (67 / 400)) (698970193 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((130875224139 / 250000) : ℝ) ≤ Real.exp (3 * (2194717 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2194717 / 500000)) (130875224139 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((669 / 4000) : ℝ) (67 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2194717 / 500000) (439177 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (669 / 4000) (67 / 400) (1397241589 / 1000000000) (698970193 / 500000000) (2194717 / 500000) (439177 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (669 / 4000) (67 / 400) (2194717 / 500000) (439177 / 100000) (50717 / 1000) (25407 / 500)
    (81893 / 500) (82759 / 500) (-125493 / 250) (2711 / 1000) (1488053 / 250) (61127 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2194717 / 500000) (130875224139 / 250000) (61127 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2194717 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2194717 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell070 :
    ∀ t ∈ Set.Icc ((67 / 400) : ℝ) (671 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((279588077 / 200000000) : ℝ) ≤ Real.exp (2 * (67 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (67 / 400)) (279588077 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((671 / 4000) : ℝ)) ≤ (1398639531 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (671 / 4000)) (1398639531 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((105391896781 / 200000) : ℝ) ≤ Real.exp (3 * (4391629 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4391629 / 1000000)) (105391896781 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((67 / 400) : ℝ) (671 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4391629 / 1000000) (2196983 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (67 / 400) (671 / 4000) (279588077 / 200000000) (1398639531 / 1000000000) (4391629 / 1000000) (2196983 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (67 / 400) (671 / 4000) (4391629 / 1000000) (2196983 / 500000) (50781 / 1000) (25439 / 500)
    (20532 / 125) (16599 / 100) (-250587 / 500) (543 / 200) (2982063 / 500) (242903 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4391629 / 1000000) (105391896781 / 200000) (242903 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4391629 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4391629 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell071 :
    ∀ t ∈ Set.Icc ((671 / 4000) : ℝ) (21 / 125), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((139863953 / 100000000) : ℝ) ≤ Real.exp (2 * (671 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (671 / 4000)) (139863953 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((21 / 125) : ℝ)) ≤ (55973561 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (21 / 125)) (55973561 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((530444103177 / 1000000) : ℝ) ≤ Real.exp (3 * (2196913 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2196913 / 500000)) (530444103177 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((671 / 4000) : ℝ) (21 / 125),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2196913 / 500000) (1099041 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (671 / 4000) (21 / 125) (139863953 / 100000000) (55973561 / 40000000) (2196913 / 500000) (1099041 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (671 / 4000) (21 / 125) (2196913 / 500000) (1099041 / 250000) (10169 / 200) (50943 / 1000)
    (82363 / 500) (166463 / 1000) (-50037 / 100) (2719 / 1000) (1494017 / 250) (96523 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2196913 / 500000) (530444103177 / 1000000) (96523 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2196913 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2196913 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell072 :
    ∀ t ∈ Set.Icc ((21 / 125) : ℝ) (673 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((87458689 / 62500000) : ℝ) ≤ Real.exp (2 * (21 / 125)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (21 / 125)) (87458689 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((673 / 4000) : ℝ)) ≤ (140003887 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (673 / 4000)) (140003887 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((533951764777 / 1000000) : ℝ) ≤ Real.exp (3 * (4396023 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4396023 / 1000000)) (533951764777 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((21 / 125) : ℝ) (673 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4396023 / 1000000) (4398363 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (21 / 125) (673 / 4000) (87458689 / 62500000) (140003887 / 100000000) (4396023 / 1000000) (4398363 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (21 / 125) (673 / 4000) (4396023 / 1000000) (4398363 / 1000000) (50909 / 1000) (51007 / 1000)
    (82599 / 500) (166937 / 1000) (-249777 / 500) (2723 / 1000) (1197607 / 200) (95889 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4396023 / 1000000) (533951764777 / 1000000) (95889 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4396023 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4396023 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell073 :
    ∀ t ∈ Set.Icc ((673 / 4000) : ℝ) (337 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1400038869 / 1000000000) : ℝ) ≤ Real.exp (2 * (673 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (673 / 4000)) (1400038869 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((337 / 2000) : ℝ)) ≤ (175092383 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (337 / 2000)) (175092383 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((107497169187 / 200000) : ℝ) ≤ Real.exp (3 * (2199111 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2199111 / 500000)) (107497169187 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((673 / 4000) : ℝ) (337 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2199111 / 500000) (2200281 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (673 / 4000) (337 / 2000) (1400038869 / 1000000000) (175092383 / 125000000) (2199111 / 500000) (2200281 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (673 / 4000) (337 / 2000) (2199111 / 500000) (2200281 / 500000) (25487 / 500) (51071 / 1000)
    (165671 / 1000) (167411 / 1000) (-249373 / 500) (2727 / 1000) (6000019 / 1000) (119073 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2199111 / 500000) (107497169187 / 200000) (119073 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2199111 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2199111 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell074 :
    ∀ t ∈ Set.Icc ((337 / 2000) : ℝ) (27 / 160), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1400739063 / 1000000000) : ℝ) ≤ Real.exp (2 * (337 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (337 / 2000)) (1400739063 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((27 / 160) : ℝ)) ≤ (1401439609 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (27 / 160)) (1401439609 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8453801841 / 15625) : ℝ) ≤ Real.exp (3 * (4400421 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4400421 / 1000000)) (8453801841 / 15625) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((337 / 2000) : ℝ) (27 / 160),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4400421 / 1000000) (4402763 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (337 / 2000) (27 / 160) (1400739063 / 1000000000) (1401439609 / 1000000000) (4400421 / 1000000) (4402763 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (337 / 2000) (27 / 160) (4400421 / 1000000) (4402763 / 1000000) (25519 / 500) (10227 / 200)
    (20768 / 125) (167887 / 1000) (-248959 / 500) (683 / 250) (751504 / 125) (11829 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4400421 / 1000000) (8453801841 / 15625) (11829 / 25000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4400421 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4400421 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell075 :
    ∀ t ∈ Set.Icc ((27 / 160) : ℝ) (169 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((175179951 / 125000000) : ℝ) ≤ Real.exp (2 * (27 / 160)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (27 / 160)) (175179951 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((169 / 1000) : ℝ)) ≤ (175267563 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (169 / 1000)) (175267563 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((68078450371 / 125000) : ℝ) ≤ Real.exp (3 * (2201311 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2201311 / 500000)) (68078450371 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((27 / 160) : ℝ) (169 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2201311 / 500000) (880993 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (27 / 160) (169 / 1000) (175179951 / 125000000) (175267563 / 125000000) (2201311 / 500000) (880993 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (27 / 160) (169 / 1000) (2201311 / 500000) (880993 / 200000) (25551 / 500) (256 / 5)
    (83309 / 500) (42091 / 250) (-497091 / 1000) (342 / 125) (1506017 / 250) (235023 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2201311 / 500000) (68078450371 / 125000) (235023 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2201311 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2201311 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell076 :
    ∀ t ∈ Set.Icc ((169 / 1000) : ℝ) (677 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1402140503 / 1000000000) : ℝ) ≤ Real.exp (2 * (169 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (169 / 1000)) (1402140503 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((677 / 4000) : ℝ)) ≤ (1402841749 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (677 / 4000)) (1402841749 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((10964745549 / 20000) : ℝ) ≤ Real.exp (3 * (550603 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (550603 / 125000)) (10964745549 / 20000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((169 / 1000) : ℝ) (677 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (550603 / 125000) (68862 / 15625) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (169 / 1000) (677 / 4000) (1402140503 / 1000000000) (1402841749 / 1000000000) (550603 / 125000) (68862 / 15625) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (169 / 1000) (677 / 4000) (550603 / 125000) (68862 / 15625) (25583 / 500) (6408 / 125)
    (83547 / 500) (84421 / 500) (-496259 / 1000) (137 / 50) (754516 / 125) (58369 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (550603 / 125000) (10964745549 / 20000) (58369 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (550603 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (550603 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell077 :
    ∀ t ∈ Set.Icc ((677 / 4000) : ℝ) (339 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((350710437 / 250000000) : ℝ) ≤ Real.exp (2 * (677 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (677 / 4000)) (350710437 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((339 / 2000) : ℝ)) ≤ (701771673 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (339 / 2000)) (701771673 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8623008301 / 15625) : ℝ) ≤ Real.exp (3 * (4407027 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4407027 / 1000000)) (8623008301 / 15625) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((677 / 4000) : ℝ) (339 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4407027 / 1000000) (1102343 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (677 / 4000) (339 / 2000) (350710437 / 250000000) (701771673 / 500000000) (4407027 / 1000000) (1102343 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (677 / 4000) (339 / 2000) (4407027 / 1000000) (1102343 / 250000) (51231 / 1000) (51329 / 1000)
    (16757 / 100) (4233 / 25) (-495421 / 1000) (343 / 125) (1512053 / 250) (115969 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4407027 / 1000000) (8623008301 / 15625) (115969 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4407027 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4407027 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell078 :
    ∀ t ∈ Set.Icc ((339 / 2000) : ℝ) (679 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((280708669 / 200000000) : ℝ) ≤ Real.exp (2 * (339 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (339 / 2000)) (280708669 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((679 / 4000) : ℝ)) ≤ (1404245293 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (679 / 4000)) (1404245293 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((69441694487 / 125000) : ℝ) ≤ Real.exp (3 * (4409231 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4409231 / 1000000)) (69441694487 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((339 / 2000) : ℝ) (679 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4409231 / 1000000) (2205789 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (339 / 2000) (679 / 4000) (280708669 / 200000000) (1404245293 / 1000000000) (4409231 / 1000000) (2205789 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (339 / 2000) (679 / 4000) (4409231 / 1000000) (2205789 / 500000) (10259 / 200) (51393 / 1000)
    (168047 / 1000) (849 / 5) (-49457 / 100) (687 / 250) (1515081 / 250) (460819 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4409231 / 1000000) (69441694487 / 125000) (460819 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4409231 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4409231 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell079 :
    ∀ t ∈ Set.Icc ((679 / 4000) : ℝ) (17 / 100), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((351061323 / 250000000) : ℝ) ≤ Real.exp (2 * (679 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (679 / 4000)) (351061323 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((17 / 100) : ℝ)) ≤ (1404947591 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (17 / 100)) (1404947591 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((34951284021 / 62500) : ℝ) ≤ Real.exp (3 * (1102859 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1102859 / 250000)) (34951284021 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((679 / 4000) : ℝ) (17 / 100),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1102859 / 250000) (551723 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (679 / 4000) (17 / 100) (351061323 / 250000000) (1404947591 / 1000000000) (1102859 / 250000) (551723 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (679 / 4000) (17 / 100) (1102859 / 250000) (551723 / 125000) (1284 / 25) (25729 / 500)
    (84263 / 500) (170281 / 1000) (-12343 / 25) (344 / 125) (1214491 / 200) (457781 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1102859 / 250000) (34951284021 / 62500) (457781 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1102859 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1102859 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityCompact_cellsBatch003 :
    ∀ t ∈ Set.Icc ((33 / 200) : ℝ) (17 / 100),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell060
      hpThetaDensityCompact_cell061)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell062
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell063
      hpThetaDensityCompact_cell064)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell065
      hpThetaDensityCompact_cell066)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell067
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell068
      hpThetaDensityCompact_cell069))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell070
      hpThetaDensityCompact_cell071)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell072
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell073
      hpThetaDensityCompact_cell074)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell075
      hpThetaDensityCompact_cell076)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell077
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell078
      hpThetaDensityCompact_cell079)))))

#print axioms hpThetaDensityCompact_cellsBatch003
end HodgeProofHP
