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
theorem hpThetaDensityExpCompact_cell080 :
    ∀ t ∈ Set.Icc ((1741 / 16000) : ℝ) (1743 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1243120809 / 1000000000) : ℝ) ≤ Real.exp (2 * (1741 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1741 / 16000)) (1243120809 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1743 / 16000) : ℝ)) ≤ (1243431629 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1743 / 16000)) (1243431629 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((61245402361 / 500000) : ℝ) ≤ Real.exp (3 * (244079 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (244079 / 62500)) (61245402361 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1741 / 16000) : ℝ) (1743 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (244079 / 62500) (781273 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1741 / 16000) (1743 / 16000) (1243120809 / 1000000000) (1243431629 / 1000000000) (244079 / 62500) (781273 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1741 / 16000) (1743 / 16000) (244079 / 62500) (781273 / 200000) (18783 / 500) (4701 / 125)
    (9658 / 125) (77943 / 1000) (-71692 / 125) (250161 / 1000000) (372573 / 100) (2089953 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (244079 / 62500) (61245402361 / 500000) (2089953 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (244079 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (244079 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell081 :
    ∀ t ∈ Set.Icc ((1743 / 16000) : ℝ) (349 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((310857907 / 250000000) : ℝ) ≤ Real.exp (2 * (1743 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1743 / 16000)) (310857907 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((349 / 3200) : ℝ)) ≤ (621871263 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (349 / 3200)) (621871263 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((61424991447 / 500000) : ℝ) ≤ Real.exp (3 * (12207 / 3125)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (12207 / 3125)) (61424991447 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1743 / 16000) : ℝ) (349 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (12207 / 3125) (1953671 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1743 / 16000) (349 / 3200) (310857907 / 250000000) (621871263 / 500000000) (12207 / 3125) (1953671 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1743 / 16000) (349 / 3200) (12207 / 3125) (1953671 / 500000) (3759 / 100) (4704 / 125)
    (77407 / 1000) (39043 / 500) (-573587 / 1000) (249617 / 1000000) (1864729 / 500) (2083843 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (12207 / 3125) (61424991447 / 500000) (2083843 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (12207 / 3125)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (12207 / 3125)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell082 :
    ∀ t ∈ Set.Icc ((349 / 3200) : ℝ) (1747 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((49749701 / 40000000) : ℝ) ≤ Real.exp (2 * (349 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (349 / 3200)) (49749701 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1747 / 16000) : ℝ)) ≤ (1244053501 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1747 / 16000)) (1244053501 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((30802645977 / 250000) : ℝ) ≤ Real.exp (3 * (3907217 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3907217 / 1000000)) (30802645977 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((349 / 3200) : ℝ) (1747 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3907217 / 1000000) (3908319 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (349 / 3200) (1747 / 16000) (49749701 / 40000000) (1244053501 / 1000000000) (3907217 / 1000000) (3908319 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (349 / 3200) (1747 / 16000) (3907217 / 1000000) (3908319 / 1000000) (7523 / 200) (37657 / 1000)
    (1551 / 20) (7823 / 100) (-286821 / 500) (249073 / 1000000) (373319 / 100) (129859 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3907217 / 1000000) (30802645977 / 250000) (129859 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3907217 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3907217 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell083 :
    ∀ t ∈ Set.Icc ((1747 / 16000) : ℝ) (1749 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2488107 / 2000000) : ℝ) ≤ Real.exp (2 * (1747 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1747 / 16000)) (2488107 / 2000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1749 / 16000) : ℝ)) ≤ (1244364553 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1749 / 16000)) (1244364553 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((12357224339 / 100000) : ℝ) ≤ Real.exp (3 * (1954097 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1954097 / 500000)) (12357224339 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1747 / 16000) : ℝ) (1749 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1954097 / 500000) (244331 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1747 / 16000) (1749 / 16000) (2488107 / 2000000) (1244364553 / 1000000000) (1954097 / 500000) (244331 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1747 / 16000) (1749 / 16000) (1954097 / 500000) (244331 / 62500) (941 / 25) (18841 / 500)
    (38847 / 500) (39187 / 500) (-573697 / 1000) (24853 / 100000) (934231 / 250) (2071663 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1954097 / 500000) (12357224339 / 100000) (2071663 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1954097 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1954097 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell084 :
    ∀ t ∈ Set.Icc ((1749 / 16000) : ℝ) (1751 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((155545569 / 125000000) : ℝ) ≤ Real.exp (2 * (1749 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1749 / 16000)) (155545569 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1751 / 16000) : ℝ)) ≤ (1244675683 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1751 / 16000)) (1244675683 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((123934964447 / 1000000) : ℝ) ≤ Real.exp (3 * (3909171 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3909171 / 1000000)) (123934964447 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1749 / 16000) : ℝ) (1751 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3909171 / 1000000) (1955137 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1749 / 16000) (1751 / 16000) (155545569 / 125000000) (1244675683 / 1000000000) (3909171 / 1000000) (1955137 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1749 / 16000) (1751 / 16000) (3909171 / 1000000) (1955137 / 500000) (4708 / 125) (18853 / 500)
    (77837 / 1000) (39259 / 500) (-286873 / 500) (247989 / 1000000) (748133 / 200) (1291 / 625000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3909171 / 1000000) (123934964447 / 1000000) (1291 / 625000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3909171 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3909171 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell085 :
    ∀ t ∈ Set.Icc ((1751 / 16000) : ℝ) (1753 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((622337841 / 500000000) : ℝ) ≤ Real.exp (2 * (1751 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1751 / 16000)) (622337841 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1753 / 16000) : ℝ)) ≤ (1244986891 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1753 / 16000)) (1244986891 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31074687549 / 250000) : ℝ) ≤ Real.exp (3 * (977537 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (977537 / 250000)) (31074687549 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1751 / 16000) : ℝ) (1753 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (977537 / 250000) (3911251 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1751 / 16000) (1753 / 16000) (622337841 / 500000000) (1244986891 / 1000000000) (977537 / 250000) (3911251 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1751 / 16000) (1753 / 16000) (977537 / 250000) (3911251 / 1000000) (37689 / 1000) (37731 / 1000)
    (77981 / 1000) (39331 / 500) (-2869 / 5) (247449 / 1000000) (748881 / 200) (411911 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (977537 / 250000) (31074687549 / 250000) (411911 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (977537 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (977537 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell086 :
    ∀ t ∈ Set.Icc ((1753 / 16000) : ℝ) (351 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((124498689 / 100000000) : ℝ) ≤ Real.exp (2 * (1753 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1753 / 16000)) (124498689 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((351 / 3200) : ℝ)) ≤ (2432223 / 1953125) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (351 / 3200)) (2432223 / 1953125) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((124663977751 / 1000000) : ℝ) ≤ Real.exp (3 * (1955563 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1955563 / 500000)) (124663977751 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1753 / 16000) : ℝ) (351 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1955563 / 500000) (3912229 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1753 / 16000) (351 / 3200) (124498689 / 100000000) (2432223 / 1953125) (1955563 / 500000) (3912229 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1753 / 16000) (351 / 3200) (1955563 / 500000) (3912229 / 1000000) (18857 / 500) (9439 / 250)
    (625 / 8) (78807 / 1000) (-573853 / 1000) (246909 / 1000000) (3748151 / 1000) (2053521 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1955563 / 500000) (124663977751 / 1000000) (2053521 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1955563 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1955563 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell087 :
    ∀ t ∈ Set.Icc ((351 / 3200) : ℝ) (1757 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((49811927 / 40000000) : ℝ) ≤ Real.exp (2 * (351 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (351 / 3200)) (49811927 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1757 / 16000) : ℝ)) ≤ (62280477 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1757 / 16000)) (62280477 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((62515139227 / 500000) : ℝ) ≤ Real.exp (3 * (489013 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (489013 / 125000)) (62515139227 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((351 / 3200) : ℝ) (1757 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (489013 / 125000) (3913207 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (351 / 3200) (1757 / 16000) (49811927 / 40000000) (62280477 / 50000000) (489013 / 125000) (3913207 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (351 / 3200) (1757 / 16000) (489013 / 125000) (3913207 / 1000000) (18869 / 500) (37781 / 1000)
    (7827 / 100) (78951 / 1000) (-114781 / 200) (24637 / 100000) (3751901 / 1000) (409501 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (489013 / 125000) (62515139227 / 500000) (409501 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (489013 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (489013 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell088 :
    ∀ t ∈ Set.Icc ((1757 / 16000) : ℝ) (1759 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1245609539 / 1000000000) : ℝ) ≤ Real.exp (2 * (1757 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1757 / 16000)) (1245609539 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1759 / 16000) : ℝ)) ≤ (1245920981 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1759 / 16000)) (1245920981 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((125397655457 / 1000000) : ℝ) ≤ Real.exp (3 * (1956541 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1956541 / 500000)) (125397655457 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1757 / 16000) : ℝ) (1759 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1956541 / 500000) (1957093 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1757 / 16000) (1759 / 16000) (1245609539 / 1000000000) (1245920981 / 1000000000) (1956541 / 500000) (1957093 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1757 / 16000) (1759 / 16000) (1956541 / 500000) (1957093 / 500000) (37763 / 1000) (7561 / 200)
    (39207 / 500) (9887 / 125) (-71744 / 125) (245833 / 1000000) (3755657 / 1000) (1020753 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1956541 / 500000) (125397655457 / 1000000) (1020753 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1956541 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1956541 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell089 :
    ∀ t ∈ Set.Icc ((1759 / 16000) : ℝ) (1761 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((62296049 / 50000000) : ℝ) ≤ Real.exp (2 * (1759 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1759 / 16000)) (62296049 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1761 / 16000) : ℝ)) ≤ (498493 / 400000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1761 / 16000)) (498493 / 400000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((125766111923 / 1000000) : ℝ) ≤ Real.exp (3 * (195703 / 50000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (195703 / 50000)) (125766111923 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1759 / 16000) : ℝ) (1761 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (195703 / 50000) (783033 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1759 / 16000) (1761 / 16000) (62296049 / 50000000) (498493 / 400000) (195703 / 50000) (783033 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1759 / 16000) (1761 / 16000) (195703 / 50000) (783033 / 200000) (9447 / 250) (3783 / 100)
    (39279 / 500) (79241 / 1000) (-286999 / 500) (15331 / 62500) (751883 / 200) (81421 / 40000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (195703 / 50000) (125766111923 / 1000000) (81421 / 40000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (195703 / 50000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (195703 / 50000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell090 :
    ∀ t ∈ Set.Icc ((1761 / 16000) : ℝ) (1763 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1246232499 / 1000000000) : ℝ) ≤ Real.exp (2 * (1761 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1761 / 16000)) (1246232499 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1763 / 16000) : ℝ)) ≤ (1246544097 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1763 / 16000)) (1246544097 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((12613602943 / 100000) : ℝ) ≤ Real.exp (3 * (3915039 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3915039 / 1000000)) (12613602943 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1761 / 16000) : ℝ) (1763 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3915039 / 1000000) (3916143 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1761 / 16000) (1763 / 16000) (1246232499 / 1000000000) (1246544097 / 1000000000) (3915039 / 1000000) (3916143 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1761 / 16000) (1763 / 16000) (3915039 / 1000000) (3916143 / 1000000) (37813 / 1000) (7571 / 200)
    (78703 / 1000) (39693 / 500) (-287027 / 500) (6119 / 25000) (3763173 / 1000) (405911 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3915039 / 1000000) (12613602943 / 100000) (405911 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3915039 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3915039 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell091 :
    ∀ t ∈ Set.Icc ((1763 / 16000) : ℝ) (353 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((38954503 / 31250000) : ℝ) ≤ Real.exp (2 * (1763 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1763 / 16000)) (38954503 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((353 / 3200) : ℝ)) ≤ (311713943 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (353 / 3200)) (311713943 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((126507034979 / 1000000) : ℝ) ≤ Real.exp (3 * (1958009 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1958009 / 500000)) (126507034979 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1763 / 16000) : ℝ) (353 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1958009 / 500000) (3917123 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1763 / 16000) (353 / 3200) (38954503 / 31250000) (311713943 / 250000000) (1958009 / 500000) (3917123 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1763 / 16000) (353 / 3200) (1958009 / 500000) (3917123 / 1000000) (18919 / 500) (947 / 25)
    (78847 / 1000) (79531 / 1000) (-574099 / 1000) (122113 / 500000) (1883471 / 500) (2023603 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1958009 / 500000) (126507034979 / 1000000) (2023603 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1958009 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1958009 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell092 :
    ∀ t ∈ Set.Icc ((353 / 3200) : ℝ) (1767 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1246855771 / 1000000000) : ℝ) ≤ Real.exp (2 * (353 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (353 / 3200)) (1246855771 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1767 / 16000) : ℝ)) ≤ (49886701 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1767 / 16000)) (49886701 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((15859891471 / 125000) : ℝ) ≤ Real.exp (3 * (3916997 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3916997 / 1000000)) (15859891471 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((353 / 3200) : ℝ) (1767 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3916997 / 1000000) (1959051 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (353 / 3200) (1767 / 16000) (1246855771 / 1000000000) (49886701 / 40000000) (3916997 / 1000000) (1959051 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (353 / 3200) (1767 / 16000) (3916997 / 1000000) (1959051 / 500000) (18931 / 500) (7581 / 200)
    (9874 / 125) (79677 / 1000) (-574149 / 1000) (60923 / 250000) (3770709 / 1000) (2017669 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3916997 / 1000000) (15859891471 / 125000) (2017669 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3916997 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3916997 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell093 :
    ∀ t ∈ Set.Icc ((1767 / 16000) : ℝ) (1769 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((311791881 / 250000000) : ℝ) ≤ Real.exp (2 * (1767 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1767 / 16000)) (311791881 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1769 / 16000) : ℝ)) ≤ (311869839 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1769 / 16000)) (311869839 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1988317547 / 15625) : ℝ) ≤ Real.exp (3 * (489747 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (489747 / 125000)) (1988317547 / 15625) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1767 / 16000) : ℝ) (1769 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (489747 / 125000) (1959541 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1767 / 16000) (1769 / 16000) (311791881 / 250000000) (311869839 / 250000000) (489747 / 125000) (1959541 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1767 / 16000) (1769 / 16000) (489747 / 125000) (1959541 / 500000) (37887 / 1000) (37929 / 1000)
    (79137 / 1000) (39911 / 500) (-71774 / 125) (6079 / 25000) (3774483 / 1000) (251469 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (489747 / 125000) (1988317547 / 15625) (251469 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (489747 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (489747 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell094 :
    ∀ t ∈ Set.Icc ((1769 / 16000) : ℝ) (1771 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((249495871 / 200000000) : ℝ) ≤ Real.exp (2 * (1769 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1769 / 16000)) (249495871 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1771 / 16000) : ℝ)) ≤ (249558253 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1771 / 16000)) (249558253 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63813497399 / 500000) : ℝ) ≤ Real.exp (3 * (979739 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (979739 / 250000)) (63813497399 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1769 / 16000) : ℝ) (1771 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (979739 / 250000) (1960031 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1769 / 16000) (1771 / 16000) (249495871 / 200000000) (249558253 / 200000000) (979739 / 250000) (1960031 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1769 / 16000) (1771 / 16000) (979739 / 250000) (1960031 / 500000) (4739 / 125) (18977 / 500)
    (79283 / 1000) (9996 / 125) (-574241 / 1000) (60657 / 250000) (188913 / 50) (1002923 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (979739 / 250000) (63813497399 / 500000) (1002923 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (979739 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (979739 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell095 :
    ∀ t ∈ Set.Icc ((1771 / 16000) : ℝ) (1773 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((38993477 / 31250000) : ℝ) ≤ Real.exp (2 * (1771 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1771 / 16000)) (38993477 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1773 / 16000) : ℝ)) ≤ (312025813 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1773 / 16000)) (312025813 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((128002769739 / 1000000) : ℝ) ≤ Real.exp (3 * (61249 / 15625)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (61249 / 15625)) (128002769739 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1771 / 16000) : ℝ) (1773 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (61249 / 15625) (1960521 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1771 / 16000) (1773 / 16000) (38993477 / 31250000) (312025813 / 250000000) (61249 / 15625) (1960521 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1771 / 16000) (1773 / 16000) (61249 / 15625) (1960521 / 500000) (37937 / 1000) (37979 / 1000)
    (19857 / 250) (40057 / 500) (-71786 / 125) (242097 / 1000000) (3782039 / 1000) (1999957 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (61249 / 15625) (128002769739 / 1000000) (1999957 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (61249 / 15625)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (61249 / 15625)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell096 :
    ∀ t ∈ Set.Icc ((1773 / 16000) : ℝ) (71 / 640), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1248103251 / 1000000000) : ℝ) ≤ Real.exp (2 * (1773 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1773 / 16000)) (1248103251 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((71 / 640) : ℝ)) ≤ (1248415317 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (71 / 640)) (1248415317 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3209491277 / 25000) : ℝ) ≤ Real.exp (3 * (980229 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (980229 / 250000)) (3209491277 / 25000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1773 / 16000) : ℝ) (71 / 640),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (980229 / 250000) (1961011 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1773 / 16000) (71 / 640) (1248103251 / 1000000000) (1248415317 / 1000000000) (980229 / 250000) (1961011 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1773 / 16000) (71 / 640) (980229 / 250000) (1961011 / 500000) (18981 / 500) (9501 / 250)
    (39787 / 500) (4013 / 50) (-114867 / 200) (7549 / 31250) (1892911 / 500) (997043 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (980229 / 250000) (3209491277 / 25000) (997043 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (980229 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (980229 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell097 :
    ∀ t ∈ Set.Icc ((71 / 640) : ℝ) (1777 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((312103829 / 250000000) : ℝ) ≤ Real.exp (2 * (71 / 640)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (71 / 640)) (312103829 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1777 / 16000) : ℝ)) ≤ (62436373 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1777 / 16000)) (62436373 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64378821039 / 500000) : ℝ) ≤ Real.exp (3 * (490237 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (490237 / 125000)) (64378821039 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((71 / 640) : ℝ) (1777 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (490237 / 125000) (3923003 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (71 / 640) (1777 / 16000) (312103829 / 250000000) (62436373 / 50000000) (490237 / 125000) (3923003 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (71 / 640) (1777 / 16000) (490237 / 125000) (3923003 / 1000000) (37987 / 1000) (38029 / 1000)
    (79719 / 1000) (40203 / 500) (-71797 / 125) (241039 / 1000000) (3789611 / 1000) (248529 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (490237 / 125000) (64378821039 / 500000) (248529 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (490237 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (490237 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell098 :
    ∀ t ∈ Set.Icc ((1777 / 16000) : ℝ) (1779 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1248727459 / 1000000000) : ℝ) ≤ Real.exp (2 * (1777 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1777 / 16000)) (1248727459 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1779 / 16000) : ℝ)) ≤ (3903249 / 3125000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1779 / 16000)) (3903249 / 3125000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((129137133411 / 1000000) : ℝ) ≤ Real.exp (3 * (3922877 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3922877 / 1000000)) (129137133411 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1777 / 16000) : ℝ) (1779 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3922877 / 1000000) (245249 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1777 / 16000) (1779 / 16000) (1248727459 / 1000000000) (3903249 / 3125000) (3922877 / 1000000) (245249 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1777 / 16000) (1779 / 16000) (3922877 / 1000000) (245249 / 62500) (38011 / 1000) (19027 / 500)
    (15973 / 200) (10069 / 125) (-287211 / 500) (240511 / 1000000) (3793403 / 1000) (1982389 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3922877 / 1000000) (129137133411 / 1000000) (1982389 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3922877 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3922877 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell099 :
    ∀ t ∈ Set.Icc ((1779 / 16000) : ℝ) (1781 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1249039679 / 1000000000) : ℝ) ≤ Real.exp (2 * (1779 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1779 / 16000)) (1249039679 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1781 / 16000) : ℝ)) ≤ (1249351979 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1781 / 16000)) (1249351979 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((129517743227 / 1000000) : ℝ) ≤ Real.exp (3 * (1961929 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1961929 / 500000)) (129517743227 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1779 / 16000) : ℝ) (1781 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1961929 / 500000) (784993 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1779 / 16000) (1781 / 16000) (1249039679 / 1000000000) (1249351979 / 1000000000) (1961929 / 500000) (784993 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1779 / 16000) (1781 / 16000) (1961929 / 500000) (784993 / 200000) (9509 / 250) (38079 / 1000)
    (80011 / 1000) (80699 / 1000) (-574467 / 1000) (14999 / 62500) (1898599 / 500) (494141 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1961929 / 500000) (129517743227 / 1000000) (494141 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1961929 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1961929 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityExpCompact_cellsBatch004 :
    ∀ t ∈ Set.Icc ((1741 / 16000) : ℝ) (1781 / 16000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell080
      hpThetaDensityExpCompact_cell081)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell082
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell083
      hpThetaDensityExpCompact_cell084)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell085
      hpThetaDensityExpCompact_cell086)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell087
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell088
      hpThetaDensityExpCompact_cell089))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell090
      hpThetaDensityExpCompact_cell091)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell092
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell093
      hpThetaDensityExpCompact_cell094)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell095
      hpThetaDensityExpCompact_cell096)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell097
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell098
      hpThetaDensityExpCompact_cell099)))))

#print axioms hpThetaDensityExpCompact_cellsBatch004
end HodgeProofHP
