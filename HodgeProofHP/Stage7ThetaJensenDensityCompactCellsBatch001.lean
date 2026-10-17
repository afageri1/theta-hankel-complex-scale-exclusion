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
theorem hpThetaDensityCompact_cell020 :
    ∀ t ∈ Set.Icc ((31 / 200) : ℝ) (621 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((681712557 / 500000000) : ℝ) ≤ Real.exp (2 * (31 / 200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (31 / 200)) (681712557 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((621 / 4000) : ℝ)) ≤ (682053499 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (621 / 4000)) (682053499 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((380633430061 / 1000000) : ℝ) ≤ Real.exp (3 * (4283199 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4283199 / 1000000)) (380633430061 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((31 / 200) : ℝ) (621 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4283199 / 1000000) (4285479 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (31 / 200) (621 / 4000) (681712557 / 500000000) (682053499 / 500000000) (4283199 / 1000000) (4285479 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (31 / 200) (621 / 4000) (4283199 / 1000000) (4285479 / 1000000) (4767 / 100) (47763 / 1000)
    (141917 / 1000) (143543 / 1000) (-534587 / 1000) (2519 / 1000) (2698283 / 500) (168141 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4283199 / 1000000) (380633430061 / 1000000) (168141 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4283199 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4283199 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell021 :
    ∀ t ∈ Set.Icc ((621 / 4000) : ℝ) (311 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1364106997 / 1000000000) : ℝ) ≤ Real.exp (2 * (621 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (621 / 4000)) (1364106997 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((311 / 2000) : ℝ)) ≤ (682394611 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (311 / 2000)) (682394611 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((95772096669 / 250000) : ℝ) ≤ Real.exp (3 * (2142671 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2142671 / 500000)) (95772096669 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((621 / 4000) : ℝ) (311 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2142671 / 500000) (2143811 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (621 / 4000) (311 / 2000) (1364106997 / 1000000000) (682394611 / 500000000) (2142671 / 500000) (2143811 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (621 / 4000) (311 / 2000) (2142671 / 500000) (2143811 / 500000) (4773 / 100) (47823 / 1000)
    (71171 / 500) (143969 / 1000) (-10681 / 20) (2523 / 1000) (5407369 / 1000) (334127 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2142671 / 500000) (95772096669 / 250000) (334127 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2142671 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2142671 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell022 :
    ∀ t ∈ Set.Icc ((311 / 2000) : ℝ) (623 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1364789221 / 1000000000) : ℝ) ≤ Real.exp (2 * (311 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (311 / 2000)) (1364789221 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((623 / 4000) : ℝ)) ≤ (1365471787 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (623 / 4000)) (1365471787 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((96389794189 / 250000) : ℝ) ≤ Real.exp (3 * (857497 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (857497 / 200000)) (96389794189 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((311 / 2000) : ℝ) (623 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (857497 / 200000) (4289767 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (311 / 2000) (623 / 4000) (1364789221 / 1000000000) (1365471787 / 1000000000) (857497 / 200000) (4289767 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (311 / 2000) (623 / 4000) (857497 / 200000) (4289767 / 1000000) (47791 / 1000) (11971 / 250)
    (142767 / 1000) (144397 / 1000) (-106699 / 200) (2527 / 1000) (2709099 / 500) (663971 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (857497 / 200000) (96389794189 / 250000) (663971 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (857497 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (857497 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell023 :
    ∀ t ∈ Set.Icc ((623 / 4000) : ℝ) (39 / 250), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((682735893 / 500000000) : ℝ) ≤ Real.exp (2 * (623 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (623 / 4000)) (682735893 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((39 / 250) : ℝ)) ≤ (683077347 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (39 / 250)) (683077347 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((7760941331 / 20000) : ℝ) ≤ Real.exp (3 * (4289629 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4289629 / 1000000)) (7760941331 / 20000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((623 / 4000) : ℝ) (39 / 250),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4289629 / 1000000) (536489 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (623 / 4000) (39 / 250) (682735893 / 500000000) (683077347 / 500000000) (4289629 / 1000000) (536489 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (623 / 4000) (39 / 250) (4289629 / 1000000) (536489 / 125000) (11963 / 250) (9589 / 200)
    (71597 / 500) (5793 / 40) (-266471 / 500) (253 / 100) (5429043 / 1000) (329857 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4289629 / 1000000) (7760941331 / 20000) (329857 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4289629 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4289629 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell024 :
    ∀ t ∈ Set.Icc ((39 / 250) : ℝ) (5 / 32), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1366154693 / 1000000000) : ℝ) ≤ Real.exp (2 * (39 / 250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (39 / 250)) (1366154693 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((5 / 32) : ℝ)) ≤ (683418971 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (5 / 32)) (683418971 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((390552181367 / 1000000) : ℝ) ≤ Real.exp (3 * (2145887 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2145887 / 500000)) (390552181367 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((39 / 250) : ℝ) (5 / 32),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2145887 / 500000) (4294059 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (39 / 250) (5 / 32) (1366154693 / 1000000000) (683418971 / 500000000) (2145887 / 500000) (4294059 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (39 / 250) (5 / 32) (2145887 / 500000) (4294059 / 1000000) (5989 / 125) (24003 / 500)
    (7181 / 50) (29051 / 200) (-266189 / 500) (1267 / 500) (2719957 / 500) (655483 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2145887 / 500000) (390552181367 / 1000000) (655483 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2145887 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2145887 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell025 :
    ∀ t ∈ Set.Icc ((5 / 32) : ℝ) (313 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1366837941 / 1000000000) : ℝ) ≤ Real.exp (2 * (5 / 32)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (5 / 32)) (1366837941 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((313 / 2000) : ℝ)) ≤ (341880383 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (313 / 2000)) (341880383 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((393075826699 / 1000000) : ℝ) ≤ Real.exp (3 * (4293921 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4293921 / 1000000)) (393075826699 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((5 / 32) : ℝ) (313 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4293921 / 1000000) (2148103 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (5 / 32) (313 / 2000) (1366837941 / 1000000000) (341880383 / 250000000) (4293921 / 1000000) (2148103 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (5 / 32) (313 / 2000) (4293921 / 1000000) (2148103 / 500000) (47973 / 1000) (48067 / 1000)
    (144049 / 1000) (29137 / 200) (-265911 / 500) (1269 / 500) (2725401 / 500) (325637 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4293921 / 1000000) (393075826699 / 1000000) (325637 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4293921 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4293921 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell026 :
    ∀ t ∈ Set.Icc ((313 / 2000) : ℝ) (627 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1367521531 / 1000000000) : ℝ) ≤ Real.exp (2 * (313 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (313 / 2000)) (1367521531 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((627 / 4000) : ℝ)) ≤ (1368205463 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (627 / 4000)) (1368205463 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((395615778979 / 1000000) : ℝ) ≤ Real.exp (3 * (1074017 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1074017 / 250000)) (395615778979 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((313 / 2000) : ℝ) (627 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1074017 / 250000) (859671 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (313 / 2000) (627 / 4000) (1367521531 / 1000000000) (1368205463 / 1000000000) (1074017 / 250000) (859671 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (313 / 2000) (627 / 4000) (1074017 / 250000) (859671 / 200000) (24017 / 500) (6016 / 125)
    (72239 / 500) (36529 / 250) (-66406 / 125) (1271 / 500) (1365429 / 250) (647093 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1074017 / 250000) (395615778979 / 1000000) (647093 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1074017 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1074017 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell027 :
    ∀ t ∈ Set.Icc ((627 / 4000) : ℝ) (157 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((684102731 / 500000000) : ℝ) ≤ Real.exp (2 * (627 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (627 / 4000)) (684102731 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((157 / 1000) : ℝ)) ≤ (1368889737 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (157 / 1000)) (1368889737 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((79634906519 / 200000) : ℝ) ≤ Real.exp (3 * (4298217 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4298217 / 1000000)) (79634906519 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((627 / 4000) : ℝ) (157 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4298217 / 1000000) (537563 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (627 / 4000) (157 / 1000) (684102731 / 500000000) (1368889737 / 1000000000) (4298217 / 1000000) (537563 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (627 / 4000) (157 / 1000) (4298217 / 1000000) (537563 / 125000) (9619 / 200) (48189 / 1000)
    (36227 / 250) (36637 / 250) (-265341 / 500) (1273 / 500) (5472647 / 1000) (128587 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4298217 / 1000000) (79634906519 / 200000) (128587 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4298217 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4298217 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell028 :
    ∀ t ∈ Set.Icc ((157 / 1000) : ℝ) (629 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((171111217 / 125000000) : ℝ) ≤ Real.exp (2 * (157 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (157 / 1000)) (171111217 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((629 / 4000) : ℝ)) ≤ (1369574353 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (629 / 4000)) (1369574353 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((80150207541 / 200000) : ℝ) ≤ Real.exp (3 * (4300367 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4300367 / 1000000)) (80150207541 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((157 / 1000) : ℝ) (629 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4300367 / 1000000) (860531 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (157 / 1000) (629 / 4000) (171111217 / 125000000) (1369574353 / 1000000000) (4300367 / 1000000) (860531 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (157 / 1000) (629 / 4000) (4300367 / 1000000) (860531 / 200000) (12039 / 250) (193 / 4)
    (145339 / 1000) (146981 / 1000) (-106021 / 200) (2549 / 1000) (1370901 / 250) (638801 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4300367 / 1000000) (80150207541 / 200000) (638801 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4300367 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4300367 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell029 :
    ∀ t ∈ Set.Icc ((629 / 4000) : ℝ) (63 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((85598397 / 62500000) : ℝ) ≤ Real.exp (2 * (629 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (629 / 4000)) (85598397 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((63 / 400) : ℝ)) ≤ (1370259311 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (63 / 400)) (1370259311 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((80668842931 / 200000) : ℝ) ≤ Real.exp (3 * (4302517 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4302517 / 1000000)) (80668842931 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((629 / 4000) : ℝ) (63 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4302517 / 1000000) (4304807 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (629 / 4000) (63 / 400) (85598397 / 62500000) (1370259311 / 1000000000) (4302517 / 1000000) (4304807 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (629 / 4000) (63 / 400) (4302517 / 1000000) (4304807 / 1000000) (48217 / 1000) (48311 / 1000)
    (14577 / 100) (29483 / 200) (-132379 / 250) (2553 / 1000) (5494583 / 1000) (317347 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4302517 / 1000000) (80668842931 / 200000) (317347 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4302517 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4302517 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell030 :
    ∀ t ∈ Set.Icc ((63 / 400) : ℝ) (631 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((137025931 / 100000000) : ℝ) ≤ Real.exp (2 * (63 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (63 / 400)) (137025931 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((631 / 4000) : ℝ)) ≤ (342736153 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (631 / 4000)) (342736153 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((405956607033 / 1000000) : ℝ) ≤ Real.exp (3 * (4304669 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4304669 / 1000000)) (405956607033 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((63 / 400) : ℝ) (631 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4304669 / 1000000) (53837 / 12500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (63 / 400) (631 / 4000) (137025931 / 100000000) (342736153 / 250000000) (4304669 / 1000000) (53837 / 12500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (63 / 400) (631 / 4000) (4304669 / 1000000) (53837 / 12500) (24139 / 500) (12093 / 250)
    (146203 / 1000) (147849 / 1000) (-528929 / 1000) (2557 / 1000) (688198 / 125) (63061 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4304669 / 1000000) (405956607033 / 1000000) (63061 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4304669 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4304669 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell031 :
    ∀ t ∈ Set.Icc ((631 / 4000) : ℝ) (79 / 500), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1370944611 / 1000000000) : ℝ) ≤ Real.exp (2 * (631 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (631 / 4000)) (1370944611 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((79 / 500) : ℝ)) ≤ (85726891 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (79 / 500)) (85726891 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((204293572493 / 500000) : ℝ) ≤ Real.exp (3 * (2153411 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2153411 / 500000)) (204293572493 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((631 / 4000) : ℝ) (79 / 500),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2153411 / 500000) (2154557 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (631 / 4000) (79 / 500) (1370944611 / 1000000000) (85726891 / 62500000) (2153411 / 500000) (2154557 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (631 / 4000) (79 / 500) (2153411 / 500000) (2154557 / 500000) (2417 / 50) (48433 / 1000)
    (36659 / 250) (29657 / 200) (-528337 / 1000) (2561 / 1000) (2758303 / 500) (12531 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2153411 / 500000) (204293572493 / 500000) (12531 / 20000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2153411 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2153411 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell032 :
    ∀ t ∈ Set.Icc ((79 / 500) : ℝ) (633 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((274326051 / 200000000) : ℝ) ≤ Real.exp (2 * (79 / 500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (79 / 500)) (274326051 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((633 / 4000) : ℝ)) ≤ (1372316243 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (633 / 4000)) (1372316243 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((205617980963 / 500000) : ℝ) ≤ Real.exp (3 * (269311 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (269311 / 62500)) (205617980963 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((79 / 500) : ℝ) (633 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (269311 / 62500) (4311269 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (79 / 500) (633 / 4000) (274326051 / 200000000) (1372316243 / 1000000000) (269311 / 62500) (4311269 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (79 / 500) (633 / 4000) (269311 / 62500) (4311269 / 1000000) (48401 / 1000) (9699 / 200)
    (14707 / 100) (148721 / 1000) (-26387 / 50) (513 / 200) (110553 / 20) (311257 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (269311 / 62500) (205617980963 / 500000) (311257 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (269311 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (269311 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell033 :
    ∀ t ∈ Set.Icc ((633 / 4000) : ℝ) (317 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((686158121 / 500000000) : ℝ) ≤ Real.exp (2 * (633 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (633 / 4000)) (686158121 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((317 / 2000) : ℝ)) ≤ (343250643 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (317 / 2000)) (343250643 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((413903192291 / 1000000) : ℝ) ≤ Real.exp (3 * (4311131 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4311131 / 1000000)) (413903192291 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((633 / 4000) : ℝ) (317 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4311131 / 1000000) (172537 / 40000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (633 / 4000) (317 / 2000) (686158121 / 500000000) (343250643 / 250000000) (4311131 / 1000000) (172537 / 40000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (633 / 4000) (317 / 2000) (4311131 / 1000000) (172537 / 40000) (24231 / 500) (12139 / 250)
    (73753 / 500) (74579 / 500) (-527139 / 1000) (2569 / 1000) (1107743 / 200) (618503 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4311131 / 1000000) (413903192291 / 1000000) (618503 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4311131 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4311131 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell034 :
    ∀ t ∈ Set.Icc ((317 / 2000) : ℝ) (127 / 800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1373002571 / 1000000000) : ℝ) ≤ Real.exp (2 * (317 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (317 / 2000)) (1373002571 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((127 / 800) : ℝ)) ≤ (274737849 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (127 / 800)) (274737849 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((416588971561 / 1000000) : ℝ) ≤ Real.exp (3 * (4313287 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4313287 / 1000000)) (416588971561 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((317 / 2000) : ℝ) (127 / 800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4313287 / 1000000) (4315583 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (317 / 2000) (127 / 800) (1373002571 / 1000000000) (274737849 / 200000000) (4313287 / 1000000) (4315583 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (317 / 2000) (127 / 800) (4313287 / 1000000) (4315583 / 1000000) (12131 / 250) (24309 / 500)
    (73971 / 500) (149597 / 1000) (-21061 / 40) (643 / 250) (5549807 / 1000) (122903 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4313287 / 1000000) (416588971561 / 1000000) (122903 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4313287 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4313287 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell035 :
    ∀ t ∈ Set.Icc ((127 / 800) : ℝ) (159 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((343422311 / 250000000) : ℝ) ≤ Real.exp (2 * (127 / 800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (127 / 800)) (343422311 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((159 / 1000) : ℝ)) ≤ (687188131 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (159 / 1000)) (687188131 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((209646718129 / 500000) : ℝ) ≤ Real.exp (3 * (1078861 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1078861 / 250000)) (209646718129 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((127 / 800) : ℝ) (159 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1078861 / 250000) (4317741 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (127 / 800) (159 / 1000) (343422311 / 250000000) (687188131 / 500000000) (1078861 / 250000) (4317741 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (127 / 800) (159 / 1000) (1078861 / 250000) (4317741 / 1000000) (9717 / 200) (48679 / 1000)
    (148379 / 1000) (37509 / 250) (-525913 / 1000) (322 / 125) (1390229 / 250) (610551 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1078861 / 250000) (209646718129 / 500000) (610551 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1078861 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1078861 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell036 :
    ∀ t ∈ Set.Icc ((159 / 1000) : ℝ) (637 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1374376261 / 1000000000) : ℝ) ≤ Real.exp (2 * (159 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (159 / 1000)) (1374376261 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((637 / 4000) : ℝ)) ≤ (687531811 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (637 / 4000)) (687531811 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((105504497501 / 250000) : ℝ) ≤ Real.exp (3 * (4317603 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4317603 / 1000000)) (105504497501 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((159 / 1000) : ℝ) (637 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4317603 / 1000000) (43199 / 10000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (159 / 1000) (637 / 4000) (1374376261 / 1000000000) (687531811 / 500000000) (4317603 / 1000000) (43199 / 10000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (159 / 1000) (637 / 4000) (4317603 / 1000000) (43199 / 10000) (48647 / 1000) (48741 / 1000)
    (148817 / 1000) (37619 / 250) (-525303 / 1000) (129 / 50) (5572047 / 1000) (60661 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4317603 / 1000000) (105504497501 / 250000) (60661 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4317603 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4317603 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell037 :
    ∀ t ∈ Set.Icc ((637 / 4000) : ℝ) (319 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1375063621 / 1000000000) : ℝ) ≤ Real.exp (2 * (637 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (637 / 4000)) (1375063621 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((319 / 2000) : ℝ)) ≤ (55030053 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (319 / 2000)) (55030053 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((84952049517 / 200000) : ℝ) ≤ Real.exp (3 * (2159881 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2159881 / 500000)) (84952049517 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((637 / 4000) : ℝ) (319 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2159881 / 500000) (4322061 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (637 / 4000) (319 / 2000) (1375063621 / 1000000000) (55030053 / 40000000) (2159881 / 500000) (4322061 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (637 / 4000) (319 / 2000) (2159881 / 500000) (4322061 / 1000000) (48709 / 1000) (48803 / 1000)
    (18657 / 125) (150917 / 1000) (-262337 / 500) (323 / 125) (1116641 / 200) (602693 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2159881 / 500000) (84952049517 / 200000) (602693 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2159881 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2159881 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell038 :
    ∀ t ∈ Set.Icc ((319 / 2000) : ℝ) (639 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((343937831 / 250000000) : ℝ) ≤ Real.exp (2 * (319 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (319 / 2000)) (343937831 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((639 / 4000) : ℝ)) ≤ (1376439373 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (639 / 4000)) (1376439373 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((427521606587 / 1000000) : ℝ) ≤ Real.exp (3 * (2160961 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2160961 / 500000)) (427521606587 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((319 / 2000) : ℝ) (639 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2160961 / 500000) (2162111 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (319 / 2000) (639 / 4000) (343937831 / 250000000) (1376439373 / 1000000000) (2160961 / 500000) (2162111 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (319 / 2000) (639 / 4000) (2160961 / 500000) (2162111 / 500000) (4877 / 100) (9773 / 200)
    (29939 / 200) (151359 / 1000) (-524047 / 1000) (647 / 250) (279719 / 50) (598801 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2160961 / 500000) (427521606587 / 1000000) (598801 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2160961 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2160961 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell039 :
    ∀ t ∈ Set.Icc ((639 / 4000) : ℝ) (4 / 25), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((344109843 / 250000000) : ℝ) ≤ Real.exp (2 * (639 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (639 / 4000)) (344109843 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4 / 25) : ℝ)) ≤ (275425553 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4 / 25)) (275425553 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((430303498701 / 1000000) : ℝ) ≤ Real.exp (3 * (1081021 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1081021 / 250000)) (430303498701 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((639 / 4000) : ℝ) (4 / 25),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1081021 / 250000) (865277 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (639 / 4000) (4 / 25) (344109843 / 250000000) (275425553 / 200000000) (1081021 / 250000) (865277 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (639 / 4000) (4 / 25) (1081021 / 250000) (865277 / 200000) (6104 / 125) (24463 / 500)
    (18767 / 125) (75901 / 500) (-104683 / 200) (324 / 125) (2802791 / 500) (594929 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1081021 / 250000) (430303498701 / 1000000) (594929 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1081021 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1081021 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityCompact_cellsBatch001 :
    ∀ t ∈ Set.Icc ((31 / 200) : ℝ) (4 / 25),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell020
      hpThetaDensityCompact_cell021)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell022
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell023
      hpThetaDensityCompact_cell024)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell025
      hpThetaDensityCompact_cell026)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell027
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell028
      hpThetaDensityCompact_cell029))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell030
      hpThetaDensityCompact_cell031)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell032
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell033
      hpThetaDensityCompact_cell034)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell035
      hpThetaDensityCompact_cell036)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell037
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell038
      hpThetaDensityCompact_cell039)))))

#print axioms hpThetaDensityCompact_cellsBatch001
end HodgeProofHP
