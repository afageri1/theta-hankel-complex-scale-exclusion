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
theorem hpThetaDensityLowerExpCompact_cell380 :
    ∀ t ∈ Set.Icc ((41659 / 512000) : ℝ) (41663 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((294179871 / 250000000) : ℝ) ≤ Real.exp (2 * (41659 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41659 / 512000)) (294179871 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41663 / 512000) : ℝ)) ≤ (1176737871 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41663 / 512000)) (1176737871 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4094512903 / 62500) : ℝ) ≤ Real.exp (3 * (462083 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (462083 / 125000)) (4094512903 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41659 / 512000) : ℝ) (41663 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (462083 / 125000) (92421 / 25000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41659 / 512000) (41663 / 512000) (294179871 / 250000000) (1176737871 / 1000000000) (462083 / 125000) (92421 / 25000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41659 / 512000) (41663 / 512000) (462083 / 125000) (92421 / 25000) (812 / 25) (32487 / 1000)
    (2479 / 50) (1242 / 25) (-553009 / 1000) (396437 / 1000000) (2988427 / 1000) (3907669 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (462083 / 125000) (4094512903 / 62500) (3907669 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (462083 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (462083 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell381 :
    ∀ t ∈ Set.Icc ((41663 / 512000) : ℝ) (41667 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((117673787 / 100000000) : ℝ) ≤ Real.exp (2 * (41663 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41663 / 512000)) (117673787 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41667 / 512000) : ℝ)) ≤ (588378129 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41667 / 512000)) (588378129 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32761803279 / 500000) : ℝ) ≤ Real.exp (3 * (1848361 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1848361 / 500000)) (32761803279 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41663 / 512000) : ℝ) (41667 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1848361 / 500000) (1848449 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41663 / 512000) (41667 / 512000) (117673787 / 100000000) (588378129 / 500000000) (1848361 / 500000) (1848449 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41663 / 512000) (41667 / 512000) (1848361 / 500000) (1848449 / 500000) (32481 / 1000) (4061 / 125)
    (49587 / 1000) (49687 / 1000) (-553019 / 1000) (198193 / 500000) (597723 / 200) (3906989 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1848361 / 500000) (32761803279 / 500000) (3906989 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1848361 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1848361 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell382 :
    ∀ t ∈ Set.Icc ((41667 / 512000) : ℝ) (41671 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1176756257 / 1000000000) : ℝ) ≤ Real.exp (2 * (41667 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41667 / 512000)) (1176756257 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41671 / 512000) : ℝ)) ≤ (235354929 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41671 / 512000)) (235354929 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4095925753 / 62500) : ℝ) ≤ Real.exp (3 * (3696779 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3696779 / 1000000)) (4095925753 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41667 / 512000) : ℝ) (41671 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3696779 / 1000000) (924239 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41667 / 512000) (41671 / 512000) (1176756257 / 1000000000) (235354929 / 200000000) (3696779 / 1000000) (924239 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41667 / 512000) (41671 / 512000) (3696779 / 1000000) (924239 / 250000) (16241 / 500) (3249 / 100)
    (49593 / 1000) (24847 / 500) (-22121 / 40) (396337 / 1000000) (1494401 / 500) (3906321 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3696779 / 1000000) (4095925753 / 62500) (3906321 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3696779 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3696779 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell383 :
    ∀ t ∈ Set.Icc ((41671 / 512000) : ℝ) (1667 / 20480), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((294193661 / 250000000) : ℝ) ≤ Real.exp (2 * (41671 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41671 / 512000)) (294193661 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1667 / 20480) : ℝ)) ≤ (147099129 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1667 / 20480)) (147099129 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16386554023 / 250000) : ℝ) ≤ Real.exp (3 * (3696837 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3696837 / 1000000)) (16386554023 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41671 / 512000) : ℝ) (1667 / 20480),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3696837 / 1000000) (3697013 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41671 / 512000) (1667 / 20480) (294193661 / 250000000) (147099129 / 125000000) (3696837 / 1000000) (3697013 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41671 / 512000) (1667 / 20480) (3696837 / 1000000) (3697013 / 1000000) (8121 / 250) (32491 / 1000)
    (49601 / 1000) (49701 / 1000) (-13826 / 25) (396287 / 1000000) (2988987 / 1000) (1952821 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3696837 / 1000000) (16386554023 / 250000) (1952821 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3696837 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3696837 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell384 :
    ∀ t ∈ Set.Icc ((1667 / 20480) : ℝ) (41679 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1176793031 / 1000000000) : ℝ) ≤ Real.exp (2 * (1667 / 20480)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1667 / 20480)) (1176793031 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41679 / 512000) : ℝ)) ≤ (58840571 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41679 / 512000)) (58840571 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((65557622121 / 1000000) : ℝ) ≤ Real.exp (3 * (739379 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (739379 / 200000)) (65557622121 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1667 / 20480) : ℝ) (41679 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (739379 / 200000) (3697071 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1667 / 20480) (41679 / 512000) (1176793031 / 1000000000) (58840571 / 50000000) (739379 / 200000) (3697071 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1667 / 20480) (41679 / 512000) (739379 / 200000) (3697071 / 1000000) (6497 / 200) (8123 / 250)
    (6201 / 125) (12427 / 250) (-11061 / 20) (99059 / 250000) (1494587 / 500) (1952481 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (739379 / 200000) (65557622121 / 1000000) (1952481 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (739379 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (739379 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell385 :
    ∀ t ∈ Set.Icc ((41679 / 512000) : ℝ) (41683 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1176811419 / 1000000000) : ℝ) ≤ Real.exp (2 * (41679 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41679 / 512000)) (1176811419 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41683 / 512000) : ℝ)) ≤ (1176829807 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41683 / 512000)) (1176829807 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32784515067 / 500000) : ℝ) ≤ Real.exp (3 * (3696953 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3696953 / 1000000)) (32784515067 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41679 / 512000) : ℝ) (41683 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3696953 / 1000000) (3697129 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41679 / 512000) (41683 / 512000) (1176811419 / 1000000000) (1176829807 / 1000000000) (3696953 / 1000000) (3697129 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41679 / 512000) (41683 / 512000) (3696953 / 1000000) (3697129 / 1000000) (32487 / 1000) (16247 / 500)
    (9923 / 200) (9943 / 200) (-27653 / 50) (198093 / 500000) (1494681 / 500) (3904283 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3696953 / 1000000) (32784515067 / 500000) (3904283 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3696953 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3696953 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell386 :
    ∀ t ∈ Set.Icc ((41683 / 512000) : ℝ) (41687 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((588414903 / 500000000) : ℝ) ≤ Real.exp (2 * (41683 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41683 / 512000)) (588414903 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41687 / 512000) : ℝ)) ≤ (294212049 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41687 / 512000)) (294212049 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1024691303 / 15625) : ℝ) ≤ Real.exp (3 * (369701 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (369701 / 100000)) (1024691303 / 15625) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41683 / 512000) : ℝ) (41687 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (369701 / 100000) (3697187 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41683 / 512000) (41687 / 512000) (588414903 / 500000000) (294212049 / 250000000) (369701 / 100000) (3697187 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41683 / 512000) (41687 / 512000) (369701 / 100000) (3697187 / 1000000) (4061 / 125) (6499 / 200)
    (49621 / 1000) (24861 / 500) (-110613 / 200) (396137 / 1000000) (2989549 / 1000) (780723 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (369701 / 100000) (1024691303 / 15625) (780723 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (369701 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (369701 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell387 :
    ∀ t ∈ Set.Icc ((41687 / 512000) : ℝ) (41691 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((235369639 / 200000000) : ℝ) ≤ Real.exp (2 * (41687 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41687 / 512000)) (235369639 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41691 / 512000) : ℝ)) ≤ (147108323 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41691 / 512000)) (147108323 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32795827671 / 500000) : ℝ) ≤ Real.exp (3 * (924267 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (924267 / 250000)) (32795827671 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41687 / 512000) : ℝ) (41691 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (924267 / 250000) (739449 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41687 / 512000) (41691 / 512000) (235369639 / 200000000) (147108323 / 125000000) (924267 / 250000) (739449 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41687 / 512000) (41691 / 512000) (924267 / 250000) (739449 / 200000) (32489 / 1000) (32497 / 1000)
    (12407 / 250) (49729 / 1000) (-138269 / 250) (396087 / 1000000) (2989737 / 1000) (487867 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (924267 / 250000) (32795827671 / 500000) (487867 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (924267 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (924267 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell388 :
    ∀ t ∈ Set.Icc ((41691 / 512000) : ℝ) (8339 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1176866583 / 1000000000) : ℝ) ≤ Real.exp (2 * (41691 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41691 / 512000)) (1176866583 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8339 / 102400) : ℝ)) ≤ (1176884973 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8339 / 102400)) (1176884973 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((65603069277 / 1000000) : ℝ) ≤ Real.exp (3 * (1848563 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1848563 / 500000)) (65603069277 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41691 / 512000) : ℝ) (8339 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1848563 / 500000) (1848651 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41691 / 512000) (8339 / 102400) (1176866583 / 1000000000) (1176884973 / 1000000000) (1848563 / 500000) (1848651 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41691 / 512000) (8339 / 102400) (1848563 / 500000) (1848651 / 500000) (32491 / 1000) (16249 / 500)
    (12409 / 250) (6217 / 125) (-55309 / 100) (99009 / 250000) (2989921 / 1000) (3902257 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1848563 / 500000) (65603069277 / 1000000) (3902257 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1848563 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1848563 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell389 :
    ∀ t ∈ Set.Icc ((8339 / 102400) : ℝ) (41699 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((294221243 / 250000000) : ℝ) ≤ Real.exp (2 * (8339 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8339 / 102400)) (294221243 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41699 / 512000) : ℝ)) ≤ (588451681 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41699 / 512000)) (588451681 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((65614485199 / 1000000) : ℝ) ≤ Real.exp (3 * (115537 / 31250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (115537 / 31250)) (65614485199 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8339 / 102400) : ℝ) (41699 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (115537 / 31250) (46217 / 12500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8339 / 102400) (41699 / 512000) (294221243 / 250000000) (588451681 / 500000000) (115537 / 31250) (46217 / 12500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8339 / 102400) (41699 / 512000) (115537 / 31250) (46217 / 12500) (8123 / 250) (32499 / 1000)
    (49643 / 1000) (49743 / 1000) (-5531 / 10) (197993 / 500000) (2990109 / 1000) (1950789 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (115537 / 31250) (65614485199 / 1000000) (1950789 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (115537 / 31250)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (115537 / 31250)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell390 :
    ∀ t ∈ Set.Icc ((41699 / 512000) : ℝ) (41703 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1176903361 / 1000000000) : ℝ) ≤ Real.exp (2 * (41699 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41699 / 512000)) (1176903361 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41703 / 512000) : ℝ)) ≤ (1176921751 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41703 / 512000)) (1176921751 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((65625706231 / 1000000) : ℝ) ≤ Real.exp (3 * (3697241 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3697241 / 1000000)) (65625706231 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41699 / 512000) : ℝ) (41703 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3697241 / 1000000) (1848709 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41699 / 512000) (41703 / 512000) (1176903361 / 1000000000) (1176921751 / 1000000000) (3697241 / 1000000) (1848709 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41699 / 512000) (41703 / 512000) (3697241 / 1000000) (1848709 / 500000) (32493 / 1000) (32501 / 1000)
    (49649 / 1000) (199 / 4) (-276553 / 500) (395937 / 1000000) (2990297 / 1000) (3900911 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3697241 / 1000000) (65625706231 / 1000000) (3900911 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3697241 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3697241 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell391 :
    ∀ t ∈ Set.Icc ((41703 / 512000) : ℝ) (41707 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((4707687 / 4000000) : ℝ) ≤ Real.exp (2 * (41703 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41703 / 512000)) (4707687 / 4000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41707 / 512000) : ℝ)) ≤ (58847007 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41707 / 512000)) (58847007 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16409281523 / 250000) : ℝ) ≤ Real.exp (3 * (3697299 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3697299 / 1000000)) (16409281523 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41703 / 512000) : ℝ) (41707 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3697299 / 1000000) (924369 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41703 / 512000) (41707 / 512000) (4707687 / 4000000) (58847007 / 50000000) (3697299 / 1000000) (924369 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41703 / 512000) (41707 / 512000) (3697299 / 1000000) (924369 / 250000) (6499 / 200) (16251 / 500)
    (6207 / 125) (49757 / 1000) (-138279 / 250) (395887 / 1000000) (747621 / 250) (487529 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3697299 / 1000000) (16409281523 / 250000) (487529 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3697299 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3697299 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell392 :
    ∀ t ∈ Set.Icc ((41707 / 512000) : ℝ) (41711 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1176940139 / 1000000000) : ℝ) ≤ Real.exp (2 * (41707 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41707 / 512000)) (1176940139 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41711 / 512000) : ℝ)) ≤ (117695853 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41711 / 512000)) (117695853 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3282427397 / 50000) : ℝ) ≤ Real.exp (3 * (3697357 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3697357 / 1000000)) (3282427397 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41707 / 512000) : ℝ) (41711 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3697357 / 1000000) (3697533 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41707 / 512000) (41711 / 512000) (1176940139 / 1000000000) (117695853 / 100000000) (3697357 / 1000000) (3697533 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41707 / 512000) (41711 / 512000) (3697357 / 1000000) (3697533 / 1000000) (4062 / 125) (32503 / 1000)
    (6208 / 125) (12441 / 250) (-553131 / 1000) (98959 / 250000) (2990669 / 1000) (1949777 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3697357 / 1000000) (3282427397 / 50000) (1949777 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3697357 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3697357 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell393 :
    ∀ t ∈ Set.Icc ((41711 / 512000) : ℝ) (8343 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1176958529 / 1000000000) : ℝ) ≤ Real.exp (2 * (41711 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41711 / 512000)) (1176958529 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8343 / 102400) : ℝ)) ≤ (29424423 / 25000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8343 / 102400)) (29424423 / 25000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1025937059 / 15625) : ℝ) ≤ Real.exp (3 * (739483 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (739483 / 200000)) (1025937059 / 15625) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41711 / 512000) : ℝ) (8343 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (739483 / 200000) (3697591 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41711 / 512000) (8343 / 102400) (1176958529 / 1000000000) (29424423 / 25000000) (739483 / 200000) (3697591 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41711 / 512000) (8343 / 102400) (739483 / 200000) (3697591 / 1000000) (32497 / 1000) (6501 / 200)
    (49671 / 1000) (49771 / 1000) (-553141 / 1000) (197893 / 500000) (373857 / 125) (31191 / 8000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (739483 / 200000) (1025937059 / 15625) (31191 / 8000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (739483 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (739483 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell394 :
    ∀ t ∈ Set.Icc ((8343 / 102400) : ℝ) (41719 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1176976919 / 1000000000) : ℝ) ≤ Real.exp (2 * (8343 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8343 / 102400)) (1176976919 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41719 / 512000) : ℝ)) ≤ (1176995311 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41719 / 512000)) (1176995311 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32835600293 / 500000) : ℝ) ≤ Real.exp (3 * (57773 / 15625)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (57773 / 15625)) (32835600293 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8343 / 102400) : ℝ) (41719 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (57773 / 15625) (3697649 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8343 / 102400) (41719 / 512000) (1176976919 / 1000000000) (1176995311 / 1000000000) (57773 / 15625) (3697649 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8343 / 102400) (41719 / 512000) (57773 / 15625) (3697649 / 1000000) (32499 / 1000) (16253 / 500)
    (49677 / 1000) (24889 / 500) (-276573 / 500) (395737 / 1000000) (747761 / 250) (3898209 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (57773 / 15625) (32835600293 / 500000) (3898209 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (57773 / 15625)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (57773 / 15625)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell395 :
    ∀ t ∈ Set.Icc ((41719 / 512000) : ℝ) (41723 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((117699531 / 100000000) : ℝ) ≤ Real.exp (2 * (41719 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41719 / 512000)) (117699531 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41723 / 512000) : ℝ)) ≤ (1177013701 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41723 / 512000)) (1177013701 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16420657091 / 250000) : ℝ) ≤ Real.exp (3 * (369753 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (369753 / 100000)) (16420657091 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41719 / 512000) : ℝ) (41723 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (369753 / 100000) (3697707 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41719 / 512000) (41723 / 512000) (117699531 / 100000000) (1177013701 / 1000000000) (369753 / 100000) (3697707 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41719 / 512000) (41723 / 512000) (369753 / 100000) (3697707 / 1000000) (65 / 2) (32507 / 1000)
    (12421 / 250) (9957 / 200) (-553157 / 1000) (197843 / 500000) (373904 / 125) (389753 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (369753 / 100000) (16420657091 / 250000) (389753 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (369753 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (369753 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell396 :
    ∀ t ∈ Set.Icc ((41723 / 512000) : ℝ) (41727 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((11770137 / 10000000) : ℝ) ≤ Real.exp (2 * (41723 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41723 / 512000)) (11770137 / 10000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41727 / 512000) : ℝ)) ≤ (294258023 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41727 / 512000)) (294258023 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6569405813 / 100000) : ℝ) ≤ Real.exp (3 * (924397 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (924397 / 250000)) (6569405813 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41723 / 512000) : ℝ) (41727 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (924397 / 250000) (739553 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41723 / 512000) (41727 / 512000) (11770137 / 10000000) (294258023 / 250000000) (924397 / 250000) (739553 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41723 / 512000) (41727 / 512000) (924397 / 250000) (739553 / 200000) (16251 / 500) (32509 / 1000)
    (49691 / 1000) (6224 / 125) (-553167 / 1000) (98909 / 250000) (2991419 / 1000) (974213 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (924397 / 250000) (6569405813 / 100000) (974213 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (924397 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (924397 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell397 :
    ∀ t ∈ Set.Icc ((41727 / 512000) : ℝ) (41731 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1177032091 / 1000000000) : ℝ) ≤ Real.exp (2 * (41727 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41727 / 512000)) (1177032091 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41731 / 512000) : ℝ)) ≤ (294262621 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41731 / 512000)) (294262621 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32852744943 / 500000) : ℝ) ≤ Real.exp (3 * (1848823 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1848823 / 500000)) (32852744943 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41727 / 512000) : ℝ) (41731 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1848823 / 500000) (1848911 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41727 / 512000) (41731 / 512000) (1177032091 / 1000000000) (294262621 / 250000000) (1848823 / 500000) (1848911 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41727 / 512000) (41731 / 512000) (1848823 / 500000) (1848911 / 500000) (32503 / 1000) (3251 / 100)
    (49699 / 1000) (49799 / 1000) (-553181 / 1000) (197793 / 500000) (747901 / 250) (1948087 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1848823 / 500000) (32852744943 / 500000) (1948087 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1848823 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1848823 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell398 :
    ∀ t ∈ Set.Icc ((41731 / 512000) : ℝ) (8347 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1177050483 / 1000000000) : ℝ) ≤ Real.exp (2 * (41731 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41731 / 512000)) (1177050483 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8347 / 102400) : ℝ)) ≤ (9416551 / 8000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8347 / 102400)) (9416551 / 8000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6571692363 / 100000) : ℝ) ≤ Real.exp (3 * (462213 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (462213 / 125000)) (6571692363 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41731 / 512000) : ℝ) (8347 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (462213 / 125000) (92447 / 25000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41731 / 512000) (8347 / 102400) (1177050483 / 1000000000) (9416551 / 8000000) (462213 / 125000) (92447 / 25000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41731 / 512000) (8347 / 102400) (462213 / 125000) (92447 / 25000) (4063 / 125) (4064 / 125)
    (24853 / 500) (24903 / 500) (-69149 / 125) (79107 / 200000) (2991791 / 1000) (486937 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (462213 / 125000) (6571692363 / 100000) (486937 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (462213 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (462213 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell399 :
    ∀ t ∈ Set.Icc ((8347 / 102400) : ℝ) (41739 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((588534437 / 500000000) : ℝ) ≤ Real.exp (2 * (8347 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8347 / 102400)) (588534437 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41739 / 512000) : ℝ)) ≤ (1177087267 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41739 / 512000)) (1177087267 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3286408109 / 50000) : ℝ) ≤ Real.exp (3 * (3697761 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3697761 / 1000000)) (3286408109 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8347 / 102400) : ℝ) (41739 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3697761 / 1000000) (1848969 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8347 / 102400) (41739 / 512000) (588534437 / 500000000) (1177087267 / 1000000000) (3697761 / 1000000) (1848969 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8347 / 102400) (41739 / 512000) (3697761 / 1000000) (1848969 / 500000) (16253 / 500) (32513 / 1000)
    (6214 / 125) (49813 / 1000) (-553197 / 1000) (197743 / 500000) (2991979 / 1000) (389483 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3697761 / 1000000) (3286408109 / 50000) (389483 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3697761 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3697761 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch019 :
    ∀ t ∈ Set.Icc ((41659 / 512000) : ℝ) (41739 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell380
      hpThetaDensityLowerExpCompact_cell381)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell382
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell383
      hpThetaDensityLowerExpCompact_cell384)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell385
      hpThetaDensityLowerExpCompact_cell386)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell387
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell388
      hpThetaDensityLowerExpCompact_cell389))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell390
      hpThetaDensityLowerExpCompact_cell391)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell392
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell393
      hpThetaDensityLowerExpCompact_cell394)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell395
      hpThetaDensityLowerExpCompact_cell396)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell397
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell398
      hpThetaDensityLowerExpCompact_cell399)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch019
end HodgeProofHP
