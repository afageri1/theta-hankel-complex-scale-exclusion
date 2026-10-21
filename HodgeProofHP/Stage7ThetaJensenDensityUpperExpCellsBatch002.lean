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
theorem hpThetaDensityUpperExpCompact_cell040 :
    ∀ t ∈ Set.Icc ((11 / 50) : ℝ) (441 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((776353609 / 500000000) : ℝ) ≤ Real.exp (2 * (11 / 50)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (11 / 50)) (776353609 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((441 / 2000) : ℝ)) ≤ (1554260703 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (441 / 2000)) (1554260703 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1132889350731 / 500000) : ℝ) ≤ Real.exp (3 * (4877829 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4877829 / 1000000)) (1132889350731 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((11 / 50) : ℝ) (441 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4877829 / 1000000) (2441433 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (11 / 50) (441 / 2000) (776353609 / 500000000) (1554260703 / 1000000000) (4877829 / 1000000) (2441433 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (11 / 50) (441 / 2000) (4877829 / 1000000) (2441433 / 500000) (527 / 8) (66103 / 1000)
    (286369 / 1000) (1454 / 5) (-76107 / 500) (26413 / 1000000) (4547673 / 500) (56493 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4877829 / 1000000) (1132889350731 / 500000) (56493 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4877829 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4877829 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell041 :
    ∀ t ∈ Set.Icc ((441 / 2000) : ℝ) (221 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((777130351 / 500000000) : ℝ) ≤ Real.exp (2 * (441 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (441 / 2000)) (777130351 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((221 / 1000) : ℝ)) ≤ (1555815741 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (221 / 1000)) (1555815741 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1149595634609 / 500000) : ℝ) ≤ Real.exp (3 * (4882709 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4882709 / 1000000)) (1149595634609 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((441 / 2000) : ℝ) (221 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4882709 / 1000000) (4887751 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (441 / 2000) (221 / 1000) (777130351 / 500000000) (1555815741 / 1000000000) (4882709 / 1000000) (4887751 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (441 / 2000) (221 / 1000) (4882709 / 1000000) (4887751 / 1000000) (16509 / 250) (13253 / 200)
    (1439 / 5) (292243 / 1000) (-73561 / 500) (6527 / 250000) (4565899 / 500) (6959 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4882709 / 1000000) (1149595634609 / 500000) (6959 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4882709 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4882709 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell042 :
    ∀ t ∈ Set.Icc ((221 / 1000) : ℝ) (443 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((77790787 / 50000000) : ℝ) ≤ Real.exp (2 * (221 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (221 / 1000)) (77790787 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((443 / 2000) : ℝ)) ≤ (311474467 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (443 / 2000)) (311474467 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((72910578487 / 31250) : ℝ) ≤ Real.exp (3 * (977519 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (977519 / 200000)) (72910578487 / 31250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((221 / 1000) : ℝ) (443 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (977519 / 200000) (4892641 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (221 / 1000) (443 / 2000) (77790787 / 50000000) (311474467 / 200000000) (977519 / 200000) (4892641 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (221 / 1000) (443 / 2000) (977519 / 200000) (4892641 / 1000000) (33099 / 500) (66427 / 1000)
    (289237 / 1000) (29369 / 100) (-70997 / 500) (5161 / 200000) (9168397 / 1000) (27431 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (977519 / 200000) (72910578487 / 31250) (27431 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (977519 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (977519 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell043 :
    ∀ t ∈ Set.Icc ((443 / 2000) : ℝ) (111 / 500), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((778686167 / 500000000) : ℝ) ≤ Real.exp (2 * (443 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (443 / 2000)) (778686167 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((111 / 500) : ℝ)) ≤ (779465243 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (111 / 500)) (779465243 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1183807673693 / 500000) : ℝ) ≤ Real.exp (3 * (978497 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (978497 / 200000)) (1183807673693 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((443 / 2000) : ℝ) (111 / 500),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (978497 / 200000) (4897537 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (443 / 2000) (111 / 500) (778686167 / 500000000) (779465243 / 500000000) (978497 / 200000) (4897537 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (443 / 2000) (111 / 500) (978497 / 200000) (4897537 / 1000000) (1659 / 25) (66589 / 1000)
    (290679 / 1000) (59029 / 200) (-34201 / 250) (12753 / 500000) (9205151 / 1000) (54063 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (978497 / 200000) (1183807673693 / 500000) (54063 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (978497 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (978497 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell044 :
    ∀ t ∈ Set.Icc ((111 / 500) : ℝ) (89 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((311786097 / 200000000) : ℝ) ≤ Real.exp (2 * (111 / 500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (111 / 500)) (311786097 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((89 / 400) : ℝ)) ≤ (390122549 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (89 / 400)) (390122549 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2402637641329 / 1000000) : ℝ) ≤ Real.exp (3 * (244869 / 50000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (244869 / 50000)) (2402637641329 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((111 / 500) : ℝ) (89 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (244869 / 50000) (1225609 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (111 / 500) (89 / 400) (311786097 / 200000000) (390122549 / 250000000) (244869 / 50000) (1225609 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (111 / 500) (89 / 400) (244869 / 50000) (1225609 / 250000) (33261 / 500) (8344 / 125)
    (292127 / 1000) (74151 / 250) (-131587 / 1000) (25209 / 1000000) (4621019 / 500) (2131 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (244869 / 50000) (2402637641329 / 1000000) (2131 / 20000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (244869 / 50000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (244869 / 50000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell045 :
    ∀ t ∈ Set.Icc ((89 / 400) : ℝ) (223 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((312098039 / 200000000) : ℝ) ≤ Real.exp (2 * (89 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (89 / 400)) (312098039 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((223 / 1000) : ℝ)) ≤ (1562051467 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (223 / 1000)) (1562051467 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2438207204207 / 1000000) : ℝ) ≤ Real.exp (3 * (4902279 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4902279 / 1000000)) (2438207204207 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((89 / 400) : ℝ) (223 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4902279 / 1000000) (4907341 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (89 / 400) (223 / 1000) (312098039 / 200000000) (1562051467 / 1000000000) (4902279 / 1000000) (4907341 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (89 / 400) (223 / 1000) (4902279 / 1000000) (4907341 / 1000000) (13337 / 200) (13383 / 200)
    (14679 / 50) (298069 / 1000) (-126307 / 1000) (6229 / 250000) (9279081 / 1000) (26249 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4902279 / 1000000) (2438207204207 / 1000000) (26249 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4902279 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4902279 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell046 :
    ∀ t ∈ Set.Icc ((223 / 1000) : ℝ) (447 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((781025733 / 500000000) : ℝ) ≤ Real.exp (2 * (223 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (223 / 1000)) (781025733 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((447 / 2000) : ℝ)) ≤ (15636143 / 10000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (447 / 2000)) (15636143 / 10000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((247434784071 / 100000) : ℝ) ≤ Real.exp (3 * (306699 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (306699 / 62500)) (247434784071 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((223 / 1000) : ℝ) (447 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (306699 / 62500) (4912251 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (223 / 1000) (447 / 2000) (781025733 / 500000000) (15636143 / 10000000) (306699 / 62500) (4912251 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (223 / 1000) (447 / 2000) (306699 / 62500) (4912251 / 1000000) (8356 / 125) (33539 / 500)
    (295039 / 1000) (14977 / 50) (-120991 / 1000) (12313 / 500000) (9316273 / 1000) (51731 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (306699 / 62500) (247434784071 / 100000) (51731 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (306699 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (306699 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell047 :
    ∀ t ∈ Set.Icc ((447 / 2000) : ℝ) (28 / 125), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1563614299 / 1000000000) : ℝ) ≤ Real.exp (2 * (447 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (447 / 2000)) (1563614299 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((28 / 125) : ℝ)) ≤ (195647337 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (28 / 125)) (195647337 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2511061791463 / 1000000) : ℝ) ≤ Real.exp (3 * (2456047 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2456047 / 500000)) (2511061791463 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((447 / 2000) : ℝ) (28 / 125),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2456047 / 500000) (2458583 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (447 / 2000) (28 / 125) (1563614299 / 1000000000) (195647337 / 125000000) (2456047 / 500000) (2458583 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (447 / 2000) (28 / 125) (2456047 / 500000) (2458583 / 500000) (67011 / 1000) (33621 / 500)
    (37063 / 125) (37627 / 125) (-28907 / 250) (24339 / 1000000) (1870723 / 200) (101949 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2456047 / 500000) (2511061791463 / 1000000) (101949 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2456047 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2456047 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell048 :
    ∀ t ∈ Set.Icc ((28 / 125) : ℝ) (449 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((313035739 / 200000000) : ℝ) ≤ Real.exp (2 * (28 / 125)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (28 / 125)) (313035739 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((449 / 2000) : ℝ)) ≤ (783372329 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (449 / 2000)) (783372329 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((101934041041 / 40000) : ℝ) ≤ Real.exp (3 * (307313 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (307313 / 62500)) (101934041041 / 40000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((28 / 125) : ℝ) (449 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (307313 / 62500) (2461043 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (28 / 125) (449 / 2000) (313035739 / 200000000) (783372329 / 500000000) (307313 / 62500) (2461043 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (28 / 125) (449 / 2000) (307313 / 62500) (2461043 / 500000) (2687 / 40) (33703 / 500)
    (297973 / 1000) (302499 / 1000) (-27553 / 250) (4811 / 200000) (9391107 / 1000) (50229 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (307313 / 62500) (101934041041 / 40000) (50229 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (307313 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (307313 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell049 :
    ∀ t ∈ Set.Icc ((449 / 2000) : ℝ) (9 / 40), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1566744657 / 1000000000) : ℝ) ≤ Real.exp (2 * (449 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (449 / 2000)) (1566744657 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9 / 40) : ℝ)) ≤ (784156093 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9 / 40)) (784156093 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((80820015709 / 31250) : ℝ) ≤ Real.exp (3 * (615241 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (615241 / 125000)) (80820015709 / 31250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((449 / 2000) : ℝ) (9 / 40),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (615241 / 125000) (492701 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (449 / 2000) (9 / 40) (1566744657 / 1000000000) (784156093 / 500000000) (615241 / 125000) (492701 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (449 / 2000) (9 / 40) (615241 / 125000) (492701 / 100000) (67339 / 1000) (67571 / 1000)
    (5989 / 20) (303987 / 1000) (-52383 / 500) (11887 / 500000) (9428743 / 1000) (49493 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (615241 / 125000) (80820015709 / 31250) (49493 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (615241 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (615241 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell050 :
    ∀ t ∈ Set.Icc ((9 / 40) : ℝ) (451 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((313662437 / 200000000) : ℝ) ≤ Real.exp (2 * (9 / 40)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9 / 40)) (313662437 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((451 / 2000) : ℝ)) ≤ (1569881283 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (451 / 2000)) (1569881283 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2624724770561 / 1000000) : ℝ) ≤ Real.exp (3 * (1231713 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1231713 / 250000)) (2624724770561 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9 / 40) : ℝ) (451 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1231713 / 250000) (246597 / 50000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (9 / 40) (451 / 2000) (313662437 / 200000000) (1569881283 / 1000000000) (1231713 / 250000) (246597 / 50000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (9 / 40) (451 / 2000) (1231713 / 250000) (246597 / 50000) (67503 / 1000) (8467 / 125)
    (300931 / 1000) (305481 / 1000) (-99257 / 1000) (2937 / 125000) (9466537 / 1000) (19507 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1231713 / 250000) (2624724770561 / 1000000) (19507 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1231713 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1231713 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell051 :
    ∀ t ∈ Set.Icc ((451 / 2000) : ℝ) (113 / 500), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((784940641 / 500000000) : ℝ) ≤ Real.exp (2 * (451 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (451 / 2000)) (784940641 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((113 / 500) : ℝ)) ≤ (1571451949 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (113 / 500)) (1571451949 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2663829589909 / 1000000) : ℝ) ≤ Real.exp (3 * (2465891 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2465891 / 500000)) (2663829589909 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((451 / 2000) : ℝ) (113 / 500),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2465891 / 500000) (2468437 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (451 / 2000) (113 / 500) (784940641 / 500000000) (1571451949 / 1000000000) (2465891 / 500000) (2468437 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (451 / 2000) (113 / 500) (2465891 / 500000) (2468437 / 500000) (16917 / 250) (67901 / 1000)
    (15121 / 50) (15349 / 50) (-46859 / 500) (1161 / 50000) (2376119 / 250) (96103 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2465891 / 500000) (2663829589909 / 1000000) (96103 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2465891 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2465891 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell052 :
    ∀ t ∈ Set.Icc ((113 / 500) : ℝ) (453 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((392862987 / 250000000) : ℝ) ≤ Real.exp (2 * (113 / 500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (113 / 500)) (392862987 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((453 / 2000) : ℝ)) ≤ (1573024187 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (453 / 2000)) (1573024187 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2703549401741 / 1000000) : ℝ) ≤ Real.exp (3 * (1234179 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1234179 / 250000)) (2703549401741 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((113 / 500) : ℝ) (453 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1234179 / 250000) (4941813 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (113 / 500) (453 / 2000) (392862987 / 250000000) (1573024187 / 1000000000) (1234179 / 250000) (4941813 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (113 / 500) (453 / 2000) (1234179 / 250000) (4941813 / 1000000) (67833 / 1000) (34033 / 500)
    (303913 / 1000) (61697 / 200) (-22031 / 250) (5737 / 250000) (9542567 / 1000) (94691 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1234179 / 250000) (2703549401741 / 1000000) (94691 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1234179 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1234179 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell053 :
    ∀ t ∈ Set.Icc ((453 / 2000) : ℝ) (91 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((786512093 / 500000000) : ℝ) ≤ Real.exp (2 * (453 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (453 / 2000)) (786512093 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((91 / 400) : ℝ)) ≤ (197021673 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (91 / 400)) (197021673 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2743902564757 / 1000000) : ℝ) ≤ Real.exp (3 * (988331 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (988331 / 200000)) (2743902564757 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((453 / 2000) : ℝ) (91 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (988331 / 200000) (4951707 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (453 / 2000) (91 / 400) (786512093 / 500000000) (197021673 / 125000000) (988331 / 200000) (4951707 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (453 / 2000) (91 / 400) (988331 / 200000) (4951707 / 1000000) (67969 / 1000) (17107 / 250)
    (151971 / 500) (312981 / 1000) (-4499 / 125) (11373 / 500000) (4809609 / 500) (46649 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (988331 / 200000) (2743902564757 / 1000000) (46649 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (988331 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (988331 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell054 :
    ∀ t ∈ Set.Icc ((91 / 400) : ℝ) (457 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1576173383 / 1000000000) : ℝ) ≤ Real.exp (2 * (91 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (91 / 400)) (1576173383 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((457 / 2000) : ℝ)) ≤ (315865777 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (457 / 2000)) (315865777 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((706637953409 / 250000) : ℝ) ≤ Real.exp (3 * (1237887 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1237887 / 250000)) (706637953409 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((91 / 400) : ℝ) (457 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1237887 / 250000) (248081 / 50000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (91 / 400) (457 / 2000) (1576173383 / 1000000000) (315865777 / 200000000) (1237887 / 250000) (248081 / 50000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (91 / 400) (457 / 2000) (1237887 / 250000) (248081 / 50000) (68301 / 1000) (34381 / 500)
    (38369 / 125) (158019 / 500) (-3028 / 125) (11107 / 500000) (4848239 / 500) (9057 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1237887 / 250000) (706637953409 / 250000) (9057 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1237887 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1237887 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell055 :
    ∀ t ∈ Set.Icc ((457 / 2000) : ℝ) (459 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((394832221 / 250000000) : ℝ) ≤ Real.exp (2 * (457 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (457 / 2000)) (394832221 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((459 / 2000) : ℝ)) ≤ (1582490703 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (459 / 2000)) (1582490703 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((145593249019 / 50000) : ℝ) ≤ Real.exp (3 * (4961461 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4961461 / 1000000)) (145593249019 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((457 / 2000) : ℝ) (459 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4961461 / 1000000) (4971553 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (457 / 2000) (459 / 2000) (394832221 / 250000000) (1582490703 / 1000000000) (4961461 / 1000000) (4971553 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (457 / 2000) (459 / 2000) (4961461 / 1000000) (4971553 / 1000000) (13727 / 200) (69097 / 1000)
    (154993 / 500) (7978 / 25) (-12261 / 1000) (21693 / 1000000) (9774359 / 1000) (87917 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4961461 / 1000000) (145593249019 / 50000) (87917 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4961461 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4961461 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell056 :
    ∀ t ∈ Set.Icc ((459 / 2000) : ℝ) (461 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((791245351 / 500000000) : ℝ) ≤ Real.exp (2 * (459 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (459 / 2000)) (791245351 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((461 / 2000) : ℝ)) ≤ (396414713 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (461 / 2000)) (396414713 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2999932836417 / 1000000) : ℝ) ≤ Real.exp (3 * (2485697 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2485697 / 500000)) (2999932836417 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((459 / 2000) : ℝ) (461 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2485697 / 500000) (2490753 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (459 / 2000) (461 / 2000) (791245351 / 500000000) (396414713 / 250000000) (2485697 / 500000) (2490753 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (459 / 2000) (461 / 2000) (2485697 / 500000) (2490753 / 500000) (68969 / 1000) (34717 / 500)
    (313043 / 1000) (12889 / 40) (-1 / 10) (21183 / 1000000) (9852867 / 1000) (10667 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2485697 / 500000) (2999932836417 / 1000000) (10667 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2485697 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2485697 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell057 :
    ∀ t ∈ Set.Icc ((461 / 2000) : ℝ) (463 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1585658851 / 1000000000) : ℝ) ≤ Real.exp (2 * (461 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (461 / 2000)) (1585658851 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((463 / 2000) : ℝ)) ≤ (1588833343 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (463 / 2000)) (1588833343 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((96589043661 / 31250) : ℝ) ≤ Real.exp (3 * (4981347 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4981347 / 1000000)) (96589043661 / 31250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((461 / 2000) : ℝ) (463 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4981347 / 1000000) (4991479 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (461 / 2000) (463 / 2000) (1585658851 / 1000000000) (1588833343 / 1000000000) (4981347 / 1000000) (4991479 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (461 / 2000) (463 / 2000) (4981347 / 1000000) (4991479 / 1000000) (34653 / 500) (17443 / 250)
    (79031 / 250) (162677 / 500) (613 / 50) (5171 / 250000) (9932007 / 1000) (41413 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4981347 / 1000000) (96589043661 / 31250) (41413 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4981347 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4981347 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell058 :
    ∀ t ∈ Set.Icc ((463 / 2000) : ℝ) (93 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((794416671 / 500000000) : ℝ) ≤ Real.exp (2 * (463 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (463 / 2000)) (794416671 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((93 / 400) : ℝ)) ≤ (1592014189 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (93 / 400)) (1592014189 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3184702489727 / 1000000) : ℝ) ≤ Real.exp (3 * (4991319 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4991319 / 1000000)) (3184702489727 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((463 / 2000) : ℝ) (93 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4991319 / 1000000) (78148 / 15625) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (463 / 2000) (93 / 400) (794416671 / 500000000) (1592014189 / 1000000000) (4991319 / 1000000) (78148 / 15625) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (463 / 2000) (93 / 400) (4991319 / 1000000) (78148 / 15625) (17411 / 250) (70111 / 1000)
    (79807 / 250) (82127 / 250) (2483 / 100) (4039 / 200000) (5005891 / 500) (16077 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4991319 / 1000000) (3184702489727 / 1000000) (16077 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4991319 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4991319 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell059 :
    ∀ t ∈ Set.Icc ((93 / 400) : ℝ) (467 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((398003547 / 250000000) : ℝ) ≤ Real.exp (2 * (93 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (93 / 400)) (398003547 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((467 / 2000) : ℝ)) ≤ (398800351 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (467 / 2000)) (398800351 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((328161180043 / 100000) : ℝ) ≤ Real.exp (3 * (156291 / 31250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (156291 / 31250)) (328161180043 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((93 / 400) : ℝ) (467 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (156291 / 31250) (1002297 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (93 / 400) (467 / 2000) (398003547 / 250000000) (398800351 / 250000000) (156291 / 31250) (1002297 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (93 / 400) (467 / 2000) (156291 / 31250) (1002297 / 200000) (69983 / 1000) (70453 / 1000)
    (322357 / 1000) (165843 / 500) (37597 / 1000) (19717 / 1000000) (5046099 / 500) (78011 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (156291 / 31250) (328161180043 / 100000) (78011 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (156291 / 31250)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (156291 / 31250)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityUpperExpCompact_cellsBatch002 :
    ∀ t ∈ Set.Icc ((11 / 50) : ℝ) (467 / 2000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell040
      hpThetaDensityUpperExpCompact_cell041)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell042
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell043
      hpThetaDensityUpperExpCompact_cell044)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell045
      hpThetaDensityUpperExpCompact_cell046)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell047
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell048
      hpThetaDensityUpperExpCompact_cell049))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell050
      hpThetaDensityUpperExpCompact_cell051)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell052
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell053
      hpThetaDensityUpperExpCompact_cell054)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell055
      hpThetaDensityUpperExpCompact_cell056)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell057
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell058
      hpThetaDensityUpperExpCompact_cell059)))))

#print axioms hpThetaDensityUpperExpCompact_cellsBatch002
end HodgeProofHP
