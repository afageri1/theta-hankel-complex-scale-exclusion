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
theorem hpThetaDensityUpperExpCompact_cell300 :
    ∀ t ∈ Set.Icc ((947 / 2000) : ℝ) (949 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2577964153 / 1000000000) : ℝ) ≤ Real.exp (2 * (947 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (947 / 2000)) (2577964153 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((949 / 2000) : ℝ)) ≤ (2583125243 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (949 / 2000)) (2583125243 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6578444431275849 / 200000) : ℝ) ≤ Real.exp (3 * (4049337 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4049337 / 500000)) (6578444431275849 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((947 / 2000) : ℝ) (949 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4049337 / 500000) (8115147 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (947 / 2000) (949 / 2000) (2577964153 / 1000000000) (2583125243 / 1000000000) (4049337 / 500000) (8115147 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (947 / 2000) (949 / 2000) (4049337 / 500000) (8115147 / 1000000) (213663 / 1000) (214831 / 1000)
    (598813 / 250) (303687 / 125) (10230847 / 500) (9 / 1000000) (8673923 / 125) (1 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4049337 / 500000) (6578444431275849 / 200000) (1 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4049337 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4049337 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell301 :
    ∀ t ∈ Set.Icc ((949 / 2000) : ℝ) (951 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((64578131 / 25000000) : ℝ) ≤ Real.exp (2 * (949 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (949 / 2000)) (64578131 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((951 / 2000) : ℝ)) ≤ (2588296663 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (951 / 2000)) (2588296663 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6895138115375367 / 200000) : ℝ) ≤ Real.exp (3 * (8114887 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (8114887 / 1000000)) (6895138115375367 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((949 / 2000) : ℝ) (951 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (8114887 / 1000000) (8131393 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (949 / 2000) (951 / 2000) (64578131 / 25000000) (2588296663 / 1000000000) (8114887 / 1000000) (8131393 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (949 / 2000) (951 / 2000) (8114887 / 1000000) (8131393 / 1000000) (214617 / 1000) (215789 / 1000)
    (2413149 / 1000) (1223791 / 500) (10351981 / 500) (9 / 1000000) (69948723 / 1000) (1 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (8114887 / 1000000) (6895138115375367 / 200000) (1 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8114887 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8114887 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell302 :
    ∀ t ∈ Set.Icc ((951 / 2000) : ℝ) (953 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2588296661 / 1000000000) : ℝ) ≤ Real.exp (2 * (951 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (951 / 2000)) (2588296661 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((953 / 2000) : ℝ)) ≤ (648369609 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (953 / 2000)) (648369609 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((18068981789819211 / 500000) : ℝ) ≤ Real.exp (3 * (8131133 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (8131133 / 1000000)) (18068981789819211 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((951 / 2000) : ℝ) (953 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (8131133 / 1000000) (1018459 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (951 / 2000) (953 / 2000) (2588296661 / 1000000000) (648369609 / 250000000) (8131133 / 1000000) (1018459 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (951 / 2000) (953 / 2000) (8131133 / 1000000) (1018459 / 125000) (8623 / 40) (27094 / 125)
    (243117 / 100) (2465793 / 1000) (20948731 / 1000) (9 / 1000000) (14102111 / 200) (1 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (8131133 / 1000000) (18068981789819211 / 500000) (1 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8131133 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8131133 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell303 :
    ∀ t ∈ Set.Icc ((953 / 2000) : ℝ) (191 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1296739217 / 500000000) : ℝ) ≤ Real.exp (2 * (953 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (953 / 2000)) (1296739217 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((191 / 400) : ℝ)) ≤ (2598670583 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (191 / 400)) (2598670583 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((37883070024862067 / 1000000) : ℝ) ≤ Real.exp (3 * (2036853 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2036853 / 250000)) (37883070024862067 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((953 / 2000) : ℝ) (191 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2036853 / 250000) (510249 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (953 / 2000) (191 / 400) (1296739217 / 500000000) (2598670583 / 1000000000) (2036853 / 250000) (510249 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (953 / 2000) (191 / 400) (2036853 / 250000) (510249 / 62500) (216537 / 1000) (217719 / 1000)
    (1224657 / 500) (310516 / 125) (2649503 / 125) (1 / 125000) (35538457 / 500) (7 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2036853 / 250000) (37883070024862067 / 1000000) (7 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2036853 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2036853 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell304 :
    ∀ t ∈ Set.Icc ((191 / 400) : ℝ) (957 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2598670581 / 1000000000) : ℝ) ≤ Real.exp (2 * (191 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (191 / 400)) (2598670581 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((957 / 2000) : ℝ)) ≤ (4166197 / 1600000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (957 / 2000)) (4166197 / 1600000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((39715134330829867 / 1000000) : ℝ) ≤ Real.exp (3 * (8163723 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (8163723 / 1000000)) (39715134330829867 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((191 / 400) : ℝ) (957 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (8163723 / 1000000) (1022541 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (191 / 400) (957 / 2000) (2598670581 / 1000000000) (4166197 / 1600000) (8163723 / 1000000) (1022541 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (191 / 400) (957 / 2000) (8163723 / 1000000) (1022541 / 125000) (217503 / 1000) (218689 / 1000)
    (2467583 / 1000) (625647 / 250) (2680731 / 125) (1 / 125000) (71647799 / 1000) (7 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (8163723 / 1000000) (39715134330829867 / 1000000) (7 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8163723 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8163723 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell305 :
    ∀ t ∈ Set.Icc ((957 / 2000) : ℝ) (959 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2603873123 / 1000000000) : ℝ) ≤ Real.exp (2 * (957 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (957 / 2000)) (2603873123 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((959 / 2000) : ℝ)) ≤ (2609086083 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (959 / 2000)) (2609086083 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((20819360776612831 / 500000) : ℝ) ≤ Real.exp (3 * (8180067 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (8180067 / 1000000)) (20819360776612831 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((957 / 2000) : ℝ) (959 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (8180067 / 1000000) (1639341 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (957 / 2000) (959 / 2000) (2603873123 / 1000000000) (2609086083 / 1000000000) (8180067 / 1000000) (1639341 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (957 / 2000) (959 / 2000) (8180067 / 1000000) (1639341 / 200000) (218473 / 1000) (27458 / 125)
    (310747 / 125) (100847 / 40) (10849121 / 500) (1 / 125000) (1805582 / 25) (7 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (8180067 / 1000000) (20819360776612831 / 500000) (7 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8180067 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8180067 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell306 :
    ∀ t ∈ Set.Icc ((959 / 2000) : ℝ) (961 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((4076697 / 1562500) : ℝ) ≤ Real.exp (2 * (959 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (959 / 2000)) (4076697 / 1562500) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((961 / 2000) : ℝ)) ≤ (2614309477 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (961 / 2000)) (2614309477 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((43658399252257979 / 1000000) : ℝ) ≤ Real.exp (3 * (8196443 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (8196443 / 1000000)) (43658399252257979 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((959 / 2000) : ℝ) (961 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (8196443 / 1000000) (1642623 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (959 / 2000) (961 / 2000) (4076697 / 1562500) (2614309477 / 1000000000) (8196443 / 1000000) (1642623 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (959 / 2000) (961 / 2000) (8196443 / 1000000) (1642623 / 200000) (27431 / 125) (220643 / 1000)
    (500899 / 200) (2539889 / 1000) (5488313 / 250) (7 / 1000000) (7280339 / 100) (3 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (8196443 / 1000000) (43658399252257979 / 1000000) (3 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8196443 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8196443 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell307 :
    ∀ t ∈ Set.Icc ((961 / 2000) : ℝ) (963 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1307154737 / 500000000) : ℝ) ≤ Real.exp (2 * (961 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (961 / 2000)) (1307154737 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((963 / 2000) : ℝ)) ≤ (81860729 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (963 / 2000)) (81860729 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((45779353549972711 / 1000000) : ℝ) ≤ Real.exp (3 * (8212853 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (8212853 / 1000000)) (45779353549972711 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((961 / 2000) : ℝ) (963 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (8212853 / 1000000) (4114779 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (961 / 2000) (963 / 2000) (1307154737 / 500000000) (81860729 / 31250000) (8212853 / 1000000) (4114779 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (961 / 2000) (963 / 2000) (8212853 / 1000000) (4114779 / 500000) (110213 / 500) (110813 / 500)
    (1261571 / 500) (2558731 / 1000) (2776357 / 125) (7 / 1000000) (14677633 / 200) (3 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (8212853 / 1000000) (45779353549972711 / 1000000) (3 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8212853 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8212853 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell308 :
    ∀ t ∈ Set.Icc ((963 / 2000) : ℝ) (193 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((104781733 / 40000000) : ℝ) ≤ Real.exp (2 * (963 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (963 / 2000)) (104781733 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((193 / 400) : ℝ)) ≤ (2624787657 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (193 / 400)) (2624787657 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6000815500908951 / 125000) : ℝ) ≤ Real.exp (3 * (1645859 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1645859 / 200000)) (6000815500908951 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((963 / 2000) : ℝ) (193 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1645859 / 200000) (8246033 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (963 / 2000) (193 / 400) (104781733 / 40000000) (2624787657 / 1000000000) (1645859 / 200000) (8246033 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (963 / 2000) (193 / 400) (1645859 / 200000) (8246033 / 1000000) (27676 / 125) (222613 / 1000)
    (508383 / 200) (25777 / 10) (4494217 / 200) (7 / 1000000) (18494401 / 250) (3 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1645859 / 200000) (6000815500908951 / 125000) (3 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1645859 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1645859 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell309 :
    ∀ t ∈ Set.Icc ((193 / 400) : ℝ) (967 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((524957531 / 200000000) : ℝ) ≤ Real.exp (2 * (193 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (193 / 400)) (524957531 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((967 / 2000) : ℝ)) ≤ (526008497 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (967 / 2000)) (526008497 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((50345507437713953 / 1000000) : ℝ) ≤ Real.exp (3 * (824577 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (824577 / 100000)) (50345507437713953 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((193 / 400) : ℝ) (967 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (824577 / 100000) (4131271 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (193 / 400) (967 / 2000) (524957531 / 200000000) (526008497 / 200000000) (824577 / 100000) (4131271 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (193 / 400) (967 / 2000) (824577 / 100000) (4131271 / 500000) (44479 / 200) (55901 / 250)
    (2560817 / 1000) (12984 / 5) (11367009 / 500) (7 / 1000000) (37285907 / 500) (3 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (824577 / 100000) (50345507437713953 / 1000000) (3 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (824577 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (824577 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell310 :
    ∀ t ∈ Set.Icc ((967 / 2000) : ℝ) (969 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2630042483 / 1000000000) : ℝ) ≤ Real.exp (2 * (967 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (967 / 2000)) (2630042483 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((969 / 2000) : ℝ)) ≤ (1317653917 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (969 / 2000)) (1317653917 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((52802061723048031 / 1000000) : ℝ) ≤ Real.exp (3 * (4131139 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4131139 / 500000)) (52802061723048031 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((967 / 2000) : ℝ) (969 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4131139 / 500000) (2069771 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (967 / 2000) (969 / 2000) (2630042483 / 1000000000) (1317653917 / 500000000) (4131139 / 500000) (2069771 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (967 / 2000) (969 / 2000) (4131139 / 500000) (2069771 / 250000) (111693 / 500) (1123 / 5)
    (322481 / 125) (2616031 / 1000) (22999639 / 1000) (3 / 500000) (15034159 / 200) (1 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4131139 / 500000) (52802061723048031 / 1000000) (1 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4131139 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4131139 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell311 :
    ∀ t ∈ Set.Icc ((969 / 2000) : ℝ) (971 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2635307831 / 1000000000) : ℝ) ≤ Real.exp (2 * (969 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (969 / 2000)) (2635307831 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((971 / 2000) : ℝ)) ≤ (660145931 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (971 / 2000)) (660145931 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2215289895843987 / 40000) : ℝ) ≤ Real.exp (3 * (8278819 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (8278819 / 1000000)) (2215289895843987 / 40000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((969 / 2000) : ℝ) (971 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (8278819 / 1000000) (4147829 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (969 / 2000) (971 / 2000) (2635307831 / 1000000000) (660145931 / 250000000) (8278819 / 1000000) (4147829 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (969 / 2000) (971 / 2000) (8278819 / 1000000) (4147829 / 500000) (224381 / 1000) (225599 / 1000)
    (2599009 / 1000) (2635391 / 1000) (11633967 / 500) (3 / 500000) (37887273 / 500) (1 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (8278819 / 1000000) (2215289895843987 / 40000) (1 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8278819 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8278819 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell312 :
    ∀ t ∈ Set.Icc ((971 / 2000) : ℝ) (973 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2640583721 / 1000000000) : ℝ) ≤ Real.exp (2 * (971 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (971 / 2000)) (2640583721 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((973 / 2000) : ℝ)) ≤ (82683443 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (973 / 2000)) (82683443 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((11618488762498237 / 200000) : ℝ) ≤ Real.exp (3 * (8295393 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (8295393 / 1000000)) (11618488762498237 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((971 / 2000) : ℝ) (973 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (8295393 / 1000000) (4156133 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (971 / 2000) (973 / 2000) (2640583721 / 1000000000) (82683443 / 31250000) (8295393 / 1000000) (4156133 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (971 / 2000) (973 / 2000) (8295393 / 1000000) (4156133 / 500000) (11269 / 50) (226603 / 1000)
    (2618301 / 1000) (663721 / 250) (11769503 / 500) (3 / 500000) (76383177 / 1000) (1 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (8295393 / 1000000) (11618488762498237 / 200000) (1 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8295393 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8295393 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell313 :
    ∀ t ∈ Set.Icc ((973 / 2000) : ℝ) (39 / 80), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2645870173 / 1000000000) : ℝ) ≤ Real.exp (2 * (973 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (973 / 2000)) (2645870173 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((39 / 80) : ℝ)) ≤ (2651167211 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (39 / 80)) (2651167211 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((60939541709230989 / 1000000) : ℝ) ≤ Real.exp (3 * (8312001 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (8312001 / 1000000)) (60939541709230989 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((973 / 2000) : ℝ) (39 / 80),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (8312001 / 1000000) (8328907 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (973 / 2000) (39 / 80) (2645870173 / 1000000000) (2651167211 / 1000000000) (8312001 / 1000000) (8328907 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (973 / 2000) (39 / 80) (8312001 / 1000000) (8328907 / 1000000) (28298 / 125) (227611 / 1000)
    (105509 / 40) (267451 / 100) (23812817 / 1000) (3 / 500000) (76996687 / 1000) (1 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (8312001 / 1000000) (60939541709230989 / 1000000) (1 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8312001 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8312001 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell314 :
    ∀ t ∈ Set.Icc ((39 / 80) : ℝ) (977 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2651167209 / 1000000000) : ℝ) ≤ Real.exp (2 * (39 / 80)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (39 / 80)) (2651167209 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((977 / 2000) : ℝ)) ≤ (664118713 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (977 / 2000)) (664118713 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31965133816918063 / 500000) : ℝ) ≤ Real.exp (3 * (8328641 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (8328641 / 1000000)) (31965133816918063 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((39 / 80) : ℝ) (977 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (8328641 / 1000000) (4172791 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (39 / 80) (977 / 2000) (2651167209 / 1000000000) (664118713 / 250000000) (8328641 / 1000000) (4172791 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (39 / 80) (977 / 2000) (8328641 / 1000000) (4172791 / 500000) (227391 / 1000) (28578 / 125)
    (66432 / 25) (269427 / 100) (24089479 / 1000) (3 / 500000) (1552303 / 20) (1 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (8328641 / 1000000) (31965133816918063 / 500000) (1 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8328641 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8328641 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell315 :
    ∀ t ∈ Set.Icc ((977 / 2000) : ℝ) (979 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2656474849 / 1000000000) : ℝ) ≤ Real.exp (2 * (977 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (977 / 2000)) (2656474849 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((979 / 2000) : ℝ)) ≤ (1330896559 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (979 / 2000)) (1330896559 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((67072423812263547 / 1000000) : ℝ) ≤ Real.exp (3 * (1669063 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1669063 / 200000)) (67072423812263547 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((977 / 2000) : ℝ) (979 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1669063 / 200000) (836229 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (977 / 2000) (979 / 2000) (2656474849 / 1000000000) (1330896559 / 500000000) (1669063 / 200000) (836229 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (977 / 2000) (979 / 2000) (1669063 / 200000) (836229 / 100000) (228403 / 1000) (5741 / 25)
    (267697 / 100) (542833 / 200) (2436893 / 100) (1 / 200000) (39119283 / 500) (1 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1669063 / 200000) (67072423812263547 / 1000000) (1 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1669063 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1669063 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell316 :
    ∀ t ∈ Set.Icc ((979 / 2000) : ℝ) (981 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((532358623 / 200000000) : ℝ) ≤ Real.exp (2 * (979 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (979 / 2000)) (532358623 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((981 / 2000) : ℝ)) ≤ (2667122031 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (981 / 2000)) (2667122031 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((70373872995300663 / 1000000) : ℝ) ≤ Real.exp (3 * (8362023 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (8362023 / 1000000)) (70373872995300663 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((979 / 2000) : ℝ) (981 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (8362023 / 1000000) (8379031 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (979 / 2000) (981 / 2000) (532358623 / 200000000) (2667122031 / 1000000000) (8362023 / 1000000) (8379031 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (979 / 2000) (981 / 2000) (8362023 / 1000000) (8379031 / 1000000) (229419 / 1000) (230661 / 1000)
    (674199 / 250) (1367097 / 500) (6162799 / 250) (1 / 200000) (78866973 / 1000) (1 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (8362023 / 1000000) (70373872995300663 / 1000000) (1 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8362023 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8362023 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell317 :
    ∀ t ∈ Set.Icc ((981 / 2000) : ℝ) (983 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2667122029 / 1000000000) : ℝ) ≤ Real.exp (2 * (981 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (981 / 2000)) (2667122029 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((983 / 2000) : ℝ)) ≤ (2672461613 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (983 / 2000)) (2672461613 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((18460617556539177 / 250000) : ℝ) ≤ Real.exp (3 * (8378763 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (8378763 / 1000000)) (18460617556539177 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((981 / 2000) : ℝ) (983 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (8378763 / 1000000) (4197903 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (981 / 2000) (983 / 2000) (2667122029 / 1000000000) (2672461613 / 1000000000) (8378763 / 1000000) (4197903 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (981 / 2000) (983 / 2000) (8378763 / 1000000) (4197903 / 500000) (230439 / 1000) (115843 / 500)
    (2716753 / 1000) (2754361 / 1000) (2493639 / 100) (1 / 200000) (39750223 / 500) (1 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (8378763 / 1000000) (18460617556539177 / 250000) (1 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8378763 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8378763 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell318 :
    ∀ t ∈ Set.Icc ((983 / 2000) : ℝ) (197 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((267246161 / 100000000) : ℝ) ≤ Real.exp (2 * (983 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (983 / 2000)) (267246161 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((197 / 400) : ℝ)) ≤ (535562377 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (197 / 400)) (535562377 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((7748753941880423 / 100000) : ℝ) ≤ Real.exp (3 * (4197769 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4197769 / 500000)) (7748753941880423 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((983 / 2000) : ℝ) (197 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4197769 / 500000) (4206307 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (983 / 2000) (197 / 400) (267246161 / 100000000) (535562377 / 200000000) (4197769 / 500000) (4206307 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (983 / 2000) (197 / 400) (4197769 / 500000) (4206307 / 500000) (28933 / 125) (58179 / 250)
    (54737 / 20) (2774663 / 1000) (12612213 / 500) (1 / 200000) (16027797 / 200) (1 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4197769 / 500000) (7748753941880423 / 100000) (1 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4197769 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4197769 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell319 :
    ∀ t ∈ Set.Icc ((197 / 400) : ℝ) (987 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1338905941 / 500000000) : ℝ) ≤ Real.exp (2 * (197 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (197 / 400)) (1338905941 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((987 / 2000) : ℝ)) ≤ (670793217 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (987 / 2000)) (670793217 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((81317824466700537 / 1000000) : ℝ) ≤ Real.exp (3 * (4206173 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4206173 / 500000)) (81317824466700537 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((197 / 400) : ℝ) (987 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4206173 / 500000) (526841 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (197 / 400) (987 / 2000) (1338905941 / 500000000) (670793217 / 250000000) (4206173 / 500000) (526841 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (197 / 400) (987 / 2000) (4206173 / 500000) (526841 / 62500) (232493 / 1000) (233749 / 1000)
    (2757083 / 1000) (349388 / 125) (12757709 / 500) (1 / 200000) (16156533 / 200) (1 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4206173 / 500000) (81317824466700537 / 1000000) (1 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4206173 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4206173 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityUpperExpCompact_cellsBatch015 :
    ∀ t ∈ Set.Icc ((947 / 2000) : ℝ) (987 / 2000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell300
      hpThetaDensityUpperExpCompact_cell301)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell302
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell303
      hpThetaDensityUpperExpCompact_cell304)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell305
      hpThetaDensityUpperExpCompact_cell306)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell307
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell308
      hpThetaDensityUpperExpCompact_cell309))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell310
      hpThetaDensityUpperExpCompact_cell311)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell312
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell313
      hpThetaDensityUpperExpCompact_cell314)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell315
      hpThetaDensityUpperExpCompact_cell316)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell317
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell318
      hpThetaDensityUpperExpCompact_cell319)))))

#print axioms hpThetaDensityUpperExpCompact_cellsBatch015
end HodgeProofHP
