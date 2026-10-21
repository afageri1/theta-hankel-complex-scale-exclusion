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
theorem hpThetaDensityExpCompact_cell040 :
    ∀ t ∈ Set.Icc ((1661 / 16000) : ℝ) (1663 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1230751551 / 1000000000) : ℝ) ≤ Real.exp (2 * (1661 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1661 / 16000)) (1230751551 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1663 / 16000) : ℝ)) ≤ (615529639 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1663 / 16000)) (615529639 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((54506062049 / 500000) : ℝ) ≤ Real.exp (3 * (773281 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (773281 / 200000)) (54506062049 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1661 / 16000) : ℝ) (1663 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (773281 / 200000) (483437 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1661 / 16000) (1663 / 16000) (1230751551 / 1000000000) (615529639 / 500000000) (773281 / 200000) (483437 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1661 / 16000) (1663 / 16000) (773281 / 200000) (483437 / 125000) (36591 / 1000) (4579 / 125)
    (8958 / 125) (36163 / 500) (-57087 / 100) (17049 / 62500) (1789821 / 500) (2348363 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (773281 / 200000) (54506062049 / 500000) (2348363 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (773281 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (773281 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell041 :
    ∀ t ∈ Set.Icc ((1663 / 16000) : ℝ) (333 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1231059277 / 1000000000) : ℝ) ≤ Real.exp (2 * (1663 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1663 / 16000)) (1231059277 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((333 / 3200) : ℝ)) ≤ (1231367081 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (333 / 3200)) (1231367081 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((109328827073 / 1000000) : ℝ) ≤ Real.exp (3 * (966843 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (966843 / 250000)) (109328827073 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1663 / 16000) : ℝ) (333 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (966843 / 250000) (3868463 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1663 / 16000) (333 / 3200) (1231059277 / 1000000000) (1231367081 / 1000000000) (966843 / 250000) (3868463 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1663 / 16000) (333 / 3200) (966843 / 250000) (3868463 / 1000000) (7323 / 200) (4582 / 125)
    (71801 / 1000) (72463 / 1000) (-570949 / 1000) (136099 / 500000) (3583223 / 1000) (58539 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (966843 / 250000) (109328827073 / 1000000) (58539 / 25000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (966843 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (966843 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell042 :
    ∀ t ∈ Set.Icc ((333 / 3200) : ℝ) (1667 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((30784177 / 25000000) : ℝ) ≤ Real.exp (2 * (333 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (333 / 3200)) (30784177 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1667 / 16000) : ℝ)) ≤ (615837481 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1667 / 16000)) (615837481 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((21929290027 / 200000) : ℝ) ≤ Real.exp (3 * (3868339 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3868339 / 1000000)) (21929290027 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((333 / 3200) : ℝ) (1667 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3868339 / 1000000) (3869431 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (333 / 3200) (1667 / 16000) (30784177 / 25000000) (615837481 / 500000000) (3868339 / 1000000) (3869431 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (333 / 3200) (1667 / 16000) (3868339 / 1000000) (3869431 / 1000000) (36639 / 1000) (917 / 25)
    (35969 / 500) (72601 / 1000) (-571023 / 1000) (271613 / 1000000) (3586811 / 1000) (2334777 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3868339 / 1000000) (21929290027 / 200000) (2334777 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3868339 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3868339 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell043 :
    ∀ t ∈ Set.Icc ((1667 / 16000) : ℝ) (1669 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1231674961 / 1000000000) : ℝ) ≤ Real.exp (2 * (1667 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1667 / 16000)) (1231674961 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1669 / 16000) : ℝ)) ≤ (1231982919 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1669 / 16000)) (1231982919 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((109964995957 / 1000000) : ℝ) ≤ Real.exp (3 * (1934653 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1934653 / 500000)) (109964995957 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1667 / 16000) : ℝ) (1669 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1934653 / 500000) (1935199 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1667 / 16000) (1669 / 16000) (1231674961 / 1000000000) (1231982919 / 1000000000) (1934653 / 500000) (1935199 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1667 / 16000) (1669 / 16000) (1934653 / 500000) (1935199 / 500000) (36663 / 1000) (7341 / 200)
    (2883 / 40) (72739 / 1000) (-5711 / 10) (27103 / 100000) (1795199 / 500) (1164007 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1934653 / 500000) (109964995957 / 1000000) (1164007 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1934653 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1934653 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell044 :
    ∀ t ∈ Set.Icc ((1669 / 16000) : ℝ) (1671 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((615991459 / 500000000) : ℝ) ≤ Real.exp (2 * (1669 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1669 / 16000)) (615991459 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1671 / 16000) : ℝ)) ≤ (1232290953 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1671 / 16000)) (1232290953 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((110284798073 / 1000000) : ℝ) ≤ Real.exp (3 * (1935137 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1935137 / 500000)) (110284798073 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1669 / 16000) : ℝ) (1671 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1935137 / 500000) (1935683 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1669 / 16000) (1671 / 16000) (615991459 / 500000000) (1232290953 / 1000000000) (1935137 / 500000) (1935683 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1669 / 16000) (1671 / 16000) (1935137 / 500000) (1935683 / 500000) (36687 / 1000) (36729 / 1000)
    (72213 / 1000) (18219 / 250) (-285589 / 500) (270447 / 1000000) (3593991 / 1000) (2321263 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1935137 / 500000) (110284798073 / 1000000) (2321263 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1935137 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1935137 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell045 :
    ∀ t ∈ Set.Icc ((1671 / 16000) : ℝ) (1673 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((154036369 / 125000000) : ℝ) ≤ Real.exp (2 * (1671 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1671 / 16000)) (154036369 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1673 / 16000) : ℝ)) ≤ (154074883 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1673 / 16000)) (154074883 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((110605530241 / 1000000) : ℝ) ≤ Real.exp (3 * (1935621 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1935621 / 500000)) (110605530241 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1671 / 16000) : ℝ) (1673 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1935621 / 500000) (1936167 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1671 / 16000) (1673 / 16000) (154036369 / 125000000) (154074883 / 125000000) (1935621 / 500000) (1936167 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1671 / 16000) (1673 / 16000) (1935621 / 500000) (1936167 / 500000) (4589 / 125) (36753 / 1000)
    (1447 / 20) (36507 / 500) (-285627 / 500) (53973 / 200000) (3597587 / 1000) (578633 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1935621 / 500000) (110605530241 / 1000000) (578633 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1935621 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1935621 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell046 :
    ∀ t ∈ Set.Icc ((1673 / 16000) : ℝ) (67 / 640), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1232599063 / 1000000000) : ℝ) ≤ Real.exp (2 * (1673 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1673 / 16000)) (1232599063 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((67 / 640) : ℝ)) ≤ (1232907253 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (67 / 640)) (1232907253 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((22185372477 / 200000) : ℝ) ≤ Real.exp (3 * (3872209 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3872209 / 1000000)) (22185372477 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1673 / 16000) : ℝ) (67 / 640),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3872209 / 1000000) (1936651 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1673 / 16000) (67 / 640) (1232599063 / 1000000000) (1232907253 / 1000000000) (3872209 / 1000000) (1936651 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1673 / 16000) (67 / 640) (3872209 / 1000000) (1936651 / 500000) (4592 / 125) (36777 / 1000)
    (9061 / 125) (73153 / 1000) (-22853 / 40) (53857 / 200000) (720237 / 200) (2307827 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3872209 / 1000000) (22185372477 / 200000) (2307827 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3872209 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3872209 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell047 :
    ∀ t ∈ Set.Icc ((67 / 640) : ℝ) (1677 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((308226813 / 250000000) : ℝ) ≤ Real.exp (2 * (67 / 640)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (67 / 640)) (308226813 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1677 / 16000) : ℝ)) ≤ (616607759 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1677 / 16000)) (616607759 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2781244889 / 25000) : ℝ) ≤ Real.exp (3 * (1936589 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1936589 / 500000)) (2781244889 / 25000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((67 / 640) : ℝ) (1677 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1936589 / 500000) (387427 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (67 / 640) (1677 / 16000) (308226813 / 250000000) (616607759 / 500000000) (1936589 / 500000) (387427 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (67 / 640) (1677 / 16000) (1936589 / 500000) (387427 / 100000) (919 / 25) (36801 / 1000)
    (36313 / 500) (73291 / 1000) (-285703 / 500) (53741 / 200000) (3604787 / 1000) (287641 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1936589 / 500000) (2781244889 / 25000) (287641 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1936589 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1936589 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell048 :
    ∀ t ∈ Set.Icc ((1677 / 16000) : ℝ) (1679 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1233215517 / 1000000000) : ℝ) ≤ Real.exp (2 * (1677 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1677 / 16000)) (1233215517 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1679 / 16000) : ℝ)) ≤ (61676193 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1679 / 16000)) (61676193 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((22314666829 / 200000) : ℝ) ≤ Real.exp (3 * (1937073 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1937073 / 500000)) (22314666829 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1677 / 16000) : ℝ) (1679 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1937073 / 500000) (3875239 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1677 / 16000) (1679 / 16000) (1233215517 / 1000000000) (61676193 / 50000000) (1937073 / 500000) (3875239 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1677 / 16000) (1679 / 16000) (1937073 / 500000) (3875239 / 1000000) (4598 / 125) (18413 / 500)
    (18191 / 250) (73429 / 1000) (-142869 / 250) (134063 / 500000) (1804197 / 500) (286807 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1937073 / 500000) (22314666829 / 200000) (286807 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1937073 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1937073 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell049 :
    ∀ t ∈ Set.Icc ((1679 / 16000) : ℝ) (1681 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1233523859 / 1000000000) : ℝ) ≤ Real.exp (2 * (1679 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1679 / 16000)) (1233523859 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1681 / 16000) : ℝ)) ≤ (30845807 / 25000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1681 / 16000)) (30845807 / 25000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((111898149343 / 1000000) : ℝ) ≤ Real.exp (3 * (775023 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (775023 / 200000)) (111898149343 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1679 / 16000) : ℝ) (1681 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (775023 / 200000) (242263 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1679 / 16000) (1681 / 16000) (1233523859 / 1000000000) (30845807 / 25000000) (775023 / 200000) (242263 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1679 / 16000) (1681 / 16000) (775023 / 200000) (242263 / 62500) (4601 / 125) (737 / 20)
    (36451 / 500) (9196 / 125) (-11431 / 20) (267549 / 1000000) (722401 / 200) (457559 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (775023 / 200000) (111898149343 / 1000000) (457559 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (775023 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (775023 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell050 :
    ∀ t ∈ Set.Icc ((1681 / 16000) : ℝ) (1683 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1233832279 / 1000000000) : ℝ) ≤ Real.exp (2 * (1681 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1681 / 16000)) (1233832279 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1683 / 16000) : ℝ)) ≤ (154267597 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1683 / 16000)) (154267597 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((28055977537 / 250000) : ℝ) ≤ Real.exp (3 * (969021 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (969021 / 250000)) (28055977537 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1681 / 16000) : ℝ) (1683 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (969021 / 250000) (3877177 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1681 / 16000) (1683 / 16000) (1233832279 / 1000000000) (154267597 / 125000000) (969021 / 250000) (3877177 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1681 / 16000) (1683 / 16000) (969021 / 250000) (3877177 / 1000000) (36833 / 1000) (18437 / 500)
    (73041 / 1000) (73707 / 1000) (-71453 / 125) (66743 / 250000) (1807809 / 500) (1140577 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (969021 / 250000) (28055977537 / 250000) (1140577 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (969021 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (969021 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell051 :
    ∀ t ∈ Set.Icc ((1683 / 16000) : ℝ) (337 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((49365631 / 40000000) : ℝ) ≤ Real.exp (2 * (1683 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1683 / 16000)) (49365631 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((337 / 3200) : ℝ)) ≤ (24688987 / 20000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (337 / 3200)) (24688987 / 20000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((28137654829 / 250000) : ℝ) ≤ Real.exp (3 * (3877053 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3877053 / 1000000)) (28137654829 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1683 / 16000) : ℝ) (337 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3877053 / 1000000) (3878147 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1683 / 16000) (337 / 3200) (49365631 / 40000000) (24688987 / 20000000) (3877053 / 1000000) (3878147 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1683 / 16000) (337 / 3200) (3877053 / 1000000) (3878147 / 1000000) (36857 / 1000) (18449 / 500)
    (73179 / 1000) (36923 / 500) (-142923 / 250) (266397 / 1000000) (1809619 / 500) (2274533 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3877053 / 1000000) (28137654829 / 250000) (2274533 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3877053 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3877053 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell052 :
    ∀ t ∈ Set.Icc ((337 / 3200) : ℝ) (1687 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1234449349 / 1000000000) : ℝ) ≤ Real.exp (2 * (337 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (337 / 3200)) (1234449349 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1687 / 16000) : ℝ)) ≤ (1234758001 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1687 / 16000)) (1234758001 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((56439139803 / 500000) : ℝ) ≤ Real.exp (3 * (1939011 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1939011 / 500000)) (56439139803 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((337 / 3200) : ℝ) (1687 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1939011 / 500000) (969779 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (337 / 3200) (1687 / 16000) (1234449349 / 1000000000) (1234758001 / 1000000000) (1939011 / 500000) (969779 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (337 / 3200) (1687 / 16000) (1939011 / 500000) (969779 / 250000) (36881 / 1000) (36923 / 1000)
    (36659 / 500) (14797 / 200) (-114353 / 200) (265823 / 1000000) (452857 / 125) (226793 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1939011 / 500000) (56439139803 / 500000) (226793 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1939011 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1939011 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell053 :
    ∀ t ∈ Set.Icc ((1687 / 16000) : ℝ) (1689 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((617379 / 500000) : ℝ) ≤ Real.exp (2 * (1687 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1687 / 16000)) (617379 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1689 / 16000) : ℝ)) ≤ (1235066729 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1689 / 16000)) (1235066729 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((113207233407 / 1000000) : ℝ) ≤ Real.exp (3 * (242437 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (242437 / 62500)) (113207233407 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1687 / 16000) : ℝ) (1689 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (242437 / 62500) (1940043 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1687 / 16000) (1689 / 16000) (617379 / 500000) (1235066729 / 1000000000) (242437 / 62500) (1940043 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1687 / 16000) (1689 / 16000) (242437 / 62500) (1940043 / 500000) (7381 / 200) (36947 / 1000)
    (73457 / 1000) (18531 / 250) (-571837 / 1000) (265249 / 1000000) (3626481 / 1000) (113067 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (242437 / 62500) (113207233407 / 1000000) (113067 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (242437 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (242437 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell054 :
    ∀ t ∈ Set.Icc ((1689 / 16000) : ℝ) (1691 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((154383341 / 125000000) : ℝ) ≤ Real.exp (2 * (1689 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1689 / 16000)) (154383341 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1691 / 16000) : ℝ)) ≤ (247075107 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1691 / 16000)) (247075107 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1774017904 / 15625) : ℝ) ≤ Real.exp (3 * (1939981 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1939981 / 500000)) (1774017904 / 15625) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1689 / 16000) : ℝ) (1691 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1939981 / 500000) (121283 / 31250) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1689 / 16000) (1691 / 16000) (154383341 / 125000000) (247075107 / 200000000) (1939981 / 500000) (121283 / 31250) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1689 / 16000) (1691 / 16000) (1939981 / 500000) (121283 / 31250) (3693 / 100) (36971 / 1000)
    (18399 / 250) (74263 / 1000) (-571909 / 1000) (264677 / 1000000) (3630109 / 1000) (2254769 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1939981 / 500000) (1774017904 / 15625) (2254769 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1939981 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1939981 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell055 :
    ∀ t ∈ Set.Icc ((1691 / 16000) : ℝ) (1693 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((617687767 / 500000000) : ℝ) ≤ Real.exp (2 * (1691 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1691 / 16000)) (617687767 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1693 / 16000) : ℝ)) ≤ (1235684417 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1693 / 16000)) (1235684417 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((22773603949 / 200000) : ℝ) ≤ Real.exp (3 * (970233 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (970233 / 250000)) (22773603949 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1691 / 16000) : ℝ) (1693 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (970233 / 250000) (3882027 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1691 / 16000) (1693 / 16000) (617687767 / 500000000) (1235684417 / 1000000000) (970233 / 250000) (3882027 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1691 / 16000) (1693 / 16000) (970233 / 250000) (3882027 / 1000000) (18477 / 500) (7399 / 200)
    (14747 / 200) (74403 / 1000) (-22879 / 40) (132053 / 500000) (3633743 / 1000) (2248217 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (970233 / 250000) (22773603949 / 200000) (2248217 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (970233 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (970233 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell056 :
    ∀ t ∈ Set.Icc ((1693 / 16000) : ℝ) (339 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((19307569 / 15625000) : ℝ) ≤ Real.exp (2 * (1693 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1693 / 16000)) (19307569 / 15625000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((339 / 3200) : ℝ)) ≤ (1235993377 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (339 / 3200)) (1235993377 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((28549964469 / 250000) : ℝ) ≤ Real.exp (3 * (1940951 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1940951 / 500000)) (28549964469 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1693 / 16000) : ℝ) (339 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1940951 / 500000) (3882997 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1693 / 16000) (339 / 3200) (19307569 / 15625000) (1235993377 / 1000000000) (1940951 / 500000) (3882997 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1693 / 16000) (339 / 3200) (1940951 / 500000) (3882997 / 1000000) (18489 / 500) (1851 / 50)
    (36937 / 500) (74543 / 1000) (-286023 / 500) (16471 / 62500) (3637377 / 1000) (448337 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1940951 / 500000) (28549964469 / 250000) (448337 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1940951 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1940951 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell057 :
    ∀ t ∈ Set.Icc ((339 / 3200) : ℝ) (1697 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((38624793 / 31250000) : ℝ) ≤ Real.exp (2 * (339 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (339 / 3200)) (38624793 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1697 / 16000) : ℝ)) ≤ (618151207 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1697 / 16000)) (618151207 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((57266503329 / 500000) : ℝ) ≤ Real.exp (3 * (3882873 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3882873 / 1000000)) (57266503329 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((339 / 3200) : ℝ) (1697 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3882873 / 1000000) (60687 / 15625) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (339 / 3200) (1697 / 16000) (38624793 / 31250000) (618151207 / 500000000) (3882873 / 1000000) (60687 / 15625) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (339 / 3200) (1697 / 16000) (3882873 / 1000000) (60687 / 15625) (37003 / 1000) (9261 / 250)
    (37007 / 500) (74683 / 1000) (-143029 / 250) (262967 / 1000000) (455127 / 125) (558791 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3882873 / 1000000) (57266503329 / 500000) (558791 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3882873 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3882873 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell058 :
    ∀ t ∈ Set.Icc ((1697 / 16000) : ℝ) (1699 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1236302413 / 1000000000) : ℝ) ≤ Real.exp (2 * (1697 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1697 / 16000)) (1236302413 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1699 / 16000) : ℝ)) ≤ (154576441 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1699 / 16000)) (154576441 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((114867127313 / 1000000) : ℝ) ≤ Real.exp (3 * (970961 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (970961 / 250000)) (114867127313 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1697 / 16000) : ℝ) (1699 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (970961 / 250000) (3884939 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1697 / 16000) (1699 / 16000) (1236302413 / 1000000000) (154576441 / 125000000) (970961 / 250000) (3884939 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1697 / 16000) (1699 / 16000) (970961 / 250000) (3884939 / 1000000) (37027 / 1000) (9267 / 250)
    (74153 / 1000) (74823 / 1000) (-114437 / 200) (262399 / 1000000) (3644659 / 1000) (1114331 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (970961 / 250000) (114867127313 / 1000000) (1114331 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (970961 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (970961 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell059 :
    ∀ t ∈ Set.Icc ((1699 / 16000) : ℝ) (1701 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1236611527 / 1000000000) : ℝ) ≤ Real.exp (2 * (1699 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1699 / 16000)) (1236611527 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1701 / 16000) : ℝ)) ≤ (1236920719 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1701 / 16000)) (1236920719 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((57601111339 / 500000) : ℝ) ≤ Real.exp (3 * (776963 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (776963 / 200000)) (57601111339 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1699 / 16000) : ℝ) (1701 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (776963 / 200000) (3885911 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1699 / 16000) (1701 / 16000) (1236611527 / 1000000000) (1236920719 / 1000000000) (776963 / 200000) (3885911 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1699 / 16000) (1701 / 16000) (776963 / 200000) (3885911 / 1000000) (37051 / 1000) (37093 / 1000)
    (74293 / 1000) (74963 / 1000) (-572249 / 1000) (32729 / 125000) (912077 / 250) (111109 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (776963 / 200000) (57601111339 / 500000) (111109 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (776963 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (776963 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityExpCompact_cellsBatch002 :
    ∀ t ∈ Set.Icc ((1661 / 16000) : ℝ) (1701 / 16000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell040
      hpThetaDensityExpCompact_cell041)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell042
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell043
      hpThetaDensityExpCompact_cell044)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell045
      hpThetaDensityExpCompact_cell046)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell047
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell048
      hpThetaDensityExpCompact_cell049))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell050
      hpThetaDensityExpCompact_cell051)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell052
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell053
      hpThetaDensityExpCompact_cell054)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell055
      hpThetaDensityExpCompact_cell056)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell057
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell058
      hpThetaDensityExpCompact_cell059)))))

#print axioms hpThetaDensityExpCompact_cellsBatch002
end HodgeProofHP
