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
theorem hpThetaDensityExpCompact_cell100 :
    ∀ t ∈ Set.Icc ((1781 / 16000) : ℝ) (1783 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((624675989 / 500000000) : ℝ) ≤ Real.exp (2 * (1781 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1781 / 16000)) (624675989 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1783 / 16000) : ℝ)) ≤ (312416089 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1783 / 16000)) (312416089 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16237434353 / 125000) : ℝ) ≤ Real.exp (3 * (3924839 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3924839 / 1000000)) (16237434353 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1781 / 16000) : ℝ) (1783 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3924839 / 1000000) (1962973 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1781 / 16000) (1783 / 16000) (624675989 / 500000000) (312416089 / 250000000) (3924839 / 1000000) (1962973 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1781 / 16000) (1783 / 16000) (3924839 / 1000000) (1962973 / 500000) (38061 / 1000) (4763 / 125)
    (40079 / 500) (16169 / 200) (-71814 / 125) (119729 / 500000) (760199 / 200) (394151 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3924839 / 1000000) (16237434353 / 125000) (394151 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3924839 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3924839 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell101 :
    ∀ t ∈ Set.Icc ((1783 / 16000) : ℝ) (357 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((249932871 / 200000000) : ℝ) ≤ Real.exp (2 * (1783 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1783 / 16000)) (249932871 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((357 / 3200) : ℝ)) ≤ (312494203 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (357 / 3200)) (312494203 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((130282331507 / 1000000) : ℝ) ≤ Real.exp (3 * (196291 / 50000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (196291 / 50000)) (130282331507 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1783 / 16000) : ℝ) (357 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (196291 / 50000) (245433 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1783 / 16000) (357 / 3200) (249932871 / 200000000) (312494203 / 250000000) (196291 / 50000) (245433 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1783 / 16000) (357 / 3200) (196291 / 50000) (245433 / 62500) (19043 / 500) (38129 / 1000)
    (10038 / 125) (10124 / 125) (-574551 / 1000) (119467 / 500000) (19024 / 5) (491241 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (196291 / 50000) (130282331507 / 1000000) (491241 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (196291 / 50000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (196291 / 50000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell102 :
    ∀ t ∈ Set.Icc ((357 / 3200) : ℝ) (1787 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1249976811 / 1000000000) : ℝ) ≤ Real.exp (2 * (357 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (357 / 3200)) (1249976811 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1787 / 16000) : ℝ)) ≤ (250057869 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1787 / 16000)) (250057869 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8166669287 / 62500) : ℝ) ≤ Real.exp (3 * (1963401 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1963401 / 500000)) (8166669287 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((357 / 3200) : ℝ) (1787 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1963401 / 500000) (392791 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (357 / 3200) (1787 / 16000) (1249976811 / 1000000000) (250057869 / 200000000) (1963401 / 500000) (392791 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (357 / 3200) (1787 / 16000) (1963401 / 500000) (392791 / 100000) (38111 / 1000) (19077 / 500)
    (1609 / 20) (81139 / 1000) (-287297 / 500) (23841 / 100000) (3808607 / 1000) (122449 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1963401 / 500000) (8166669287 / 62500) (122449 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1963401 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1963401 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell103 :
    ∀ t ∈ Set.Icc ((1787 / 16000) : ℝ) (1789 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((19535771 / 15625000) : ℝ) ≤ Real.exp (2 * (1787 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1787 / 16000)) (19535771 / 15625000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1789 / 16000) : ℝ)) ≤ (312650489 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1789 / 16000)) (312650489 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((131051826561 / 1000000) : ℝ) ≤ Real.exp (3 * (3927783 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3927783 / 1000000)) (131051826561 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1787 / 16000) : ℝ) (1789 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3927783 / 1000000) (982223 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1787 / 16000) (1789 / 16000) (19535771 / 15625000) (312650489 / 250000000) (3927783 / 1000000) (982223 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1787 / 16000) (1789 / 16000) (3927783 / 1000000) (982223 / 250000) (4767 / 125) (38179 / 1000)
    (80597 / 1000) (81287 / 1000) (-71829 / 125) (3717 / 15625) (3812417 / 1000) (976713 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3927783 / 1000000) (131051826561 / 1000000) (976713 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3927783 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3927783 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell104 :
    ∀ t ∈ Set.Icc ((1789 / 16000) : ℝ) (1791 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((250120391 / 200000000) : ℝ) ≤ Real.exp (2 * (1789 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1789 / 16000)) (250120391 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1791 / 16000) : ℝ)) ≤ (625457323 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1791 / 16000)) (625457323 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((131438868227 / 1000000) : ℝ) ≤ Real.exp (3 * (1964383 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1964383 / 500000)) (131438868227 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1789 / 16000) : ℝ) (1791 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1964383 / 500000) (1964937 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1789 / 16000) (1791 / 16000) (250120391 / 200000000) (625457323 / 500000000) (1964383 / 500000) (1964937 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1789 / 16000) (1791 / 16000) (1964383 / 500000) (1964937 / 500000) (38161 / 1000) (9551 / 250)
    (10093 / 125) (81433 / 1000) (-574679 / 1000) (47473 / 200000) (381623 / 100) (973837 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1964383 / 500000) (131438868227 / 1000000) (973837 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1964383 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1964383 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell105 :
    ∀ t ∈ Set.Icc ((1791 / 16000) : ℝ) (1793 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((250182929 / 200000000) : ℝ) ≤ Real.exp (2 * (1791 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1791 / 16000)) (250182929 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1793 / 16000) : ℝ)) ≤ (625613707 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1793 / 16000)) (625613707 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((131826657479 / 1000000) : ℝ) ≤ Real.exp (3 * (982437 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (982437 / 250000)) (131826657479 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1791 / 16000) : ℝ) (1793 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (982437 / 250000) (3930857 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1791 / 16000) (1793 / 16000) (250182929 / 200000000) (625613707 / 500000000) (982437 / 250000) (3930857 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1791 / 16000) (1793 / 16000) (982437 / 250000) (3930857 / 1000000) (19093 / 500) (38229 / 1000)
    (80891 / 1000) (81581 / 1000) (-114943 / 200) (59211 / 250000) (76401 / 20) (388389 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (982437 / 250000) (131826657479 / 1000000) (388389 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (982437 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (982437 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell106 :
    ∀ t ∈ Set.Icc ((1793 / 16000) : ℝ) (359 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1251227413 / 1000000000) : ℝ) ≤ Real.exp (2 * (1793 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1793 / 16000)) (1251227413 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((359 / 3200) : ℝ)) ≤ (62577013 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (359 / 3200)) (62577013 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66107795419 / 500000) : ℝ) ≤ Real.exp (3 * (393073 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (393073 / 100000)) (66107795419 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1793 / 16000) : ℝ) (359 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (393073 / 100000) (3931839 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1793 / 16000) (359 / 3200) (1251227413 / 1000000000) (62577013 / 50000000) (393073 / 100000) (3931839 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1793 / 16000) (359 / 3200) (393073 / 100000) (3931839 / 1000000) (38211 / 1000) (19127 / 500)
    (40519 / 500) (81729 / 1000) (-143689 / 250) (9453 / 40000) (955967 / 250) (242029 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (393073 / 100000) (66107795419 / 500000) (242029 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (393073 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (393073 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell107 :
    ∀ t ∈ Set.Icc ((359 / 3200) : ℝ) (1797 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1251540259 / 1000000000) : ℝ) ≤ Real.exp (2 * (359 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (359 / 3200)) (1251540259 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1797 / 16000) : ℝ)) ≤ (9780103 / 7812500) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1797 / 16000)) (9780103 / 7812500) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16575758687 / 125000) : ℝ) ≤ Real.exp (3 * (3931713 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3931713 / 1000000)) (16575758687 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((359 / 3200) : ℝ) (1797 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3931713 / 1000000) (1966411 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (359 / 3200) (1797 / 16000) (1251540259 / 1000000000) (9780103 / 7812500) (3931713 / 1000000) (1966411 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (359 / 3200) (1797 / 16000) (3931713 / 1000000) (1966411 / 500000) (9559 / 250) (38279 / 1000)
    (16237 / 200) (20469 / 250) (-143699 / 250) (117903 / 500000) (1913847 / 500) (1930531 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3931713 / 1000000) (16575758687 / 125000) (1930531 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3931713 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3931713 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell108 :
    ∀ t ∈ Set.Icc ((1797 / 16000) : ℝ) (1799 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1251853183 / 1000000000) : ℝ) ≤ Real.exp (2 * (1797 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1797 / 16000)) (1251853183 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1799 / 16000) : ℝ)) ≤ (626083093 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1799 / 16000)) (626083093 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((132997701371 / 1000000) : ℝ) ≤ Real.exp (3 * (491587 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (491587 / 125000)) (132997701371 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1797 / 16000) : ℝ) (1799 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (491587 / 125000) (1966903 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1797 / 16000) (1799 / 16000) (1251853183 / 1000000000) (626083093 / 500000000) (491587 / 125000) (1966903 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1797 / 16000) (1799 / 16000) (491587 / 125000) (1966903 / 500000) (38261 / 1000) (4788 / 125)
    (81333 / 1000) (10253 / 125) (-574831 / 1000) (29411 / 125000) (1915763 / 500) (962423 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (491587 / 125000) (132997701371 / 1000000) (962423 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (491587 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (491587 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell109 :
    ∀ t ∈ Set.Icc ((1799 / 16000) : ℝ) (1801 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((250433237 / 200000000) : ℝ) ≤ Real.exp (2 * (1799 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1799 / 16000)) (250433237 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1801 / 16000) : ℝ)) ≤ (1252479267 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1801 / 16000)) (1252479267 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3334772251 / 25000) : ℝ) ≤ Real.exp (3 * (49171 / 12500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (49171 / 12500)) (3334772251 / 25000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1799 / 16000) : ℝ) (1801 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (49171 / 12500) (3934789 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1799 / 16000) (1801 / 16000) (250433237 / 200000000) (1252479267 / 1000000000) (49171 / 12500) (3934789 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1799 / 16000) (1801 / 16000) (49171 / 12500) (3934789 / 1000000) (19143 / 500) (38329 / 1000)
    (81481 / 1000) (20543 / 250) (-4599 / 8) (23477 / 100000) (3835357 / 1000) (479793 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (49171 / 12500) (3334772251 / 25000) (479793 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (49171 / 12500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (49171 / 12500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell110 :
    ∀ t ∈ Set.Icc ((1801 / 16000) : ℝ) (1803 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((626239633 / 500000000) : ℝ) ≤ Real.exp (2 * (1801 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1801 / 16000)) (626239633 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1803 / 16000) : ℝ)) ≤ (626396213 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1803 / 16000)) (626396213 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((133784839757 / 1000000) : ℝ) ≤ Real.exp (3 * (3934663 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3934663 / 1000000)) (133784839757 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1801 / 16000) : ℝ) (1803 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3934663 / 1000000) (3935773 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1801 / 16000) (1803 / 16000) (626239633 / 500000000) (626396213 / 500000000) (3934663 / 1000000) (3935773 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1801 / 16000) (1803 / 16000) (3934663 / 1000000) (3935773 / 1000000) (38311 / 1000) (19177 / 500)
    (20407 / 250) (82321 / 1000) (-143727 / 250) (46851 / 200000) (767839 / 200) (1913521 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3934663 / 1000000) (133784839757 / 1000000) (1913521 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3934663 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3934663 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell111 :
    ∀ t ∈ Set.Icc ((1803 / 16000) : ℝ) (361 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((50111697 / 40000000) : ℝ) ≤ Real.exp (2 * (1803 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1803 / 16000)) (50111697 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((361 / 3200) : ℝ)) ≤ (1253105663 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (361 / 3200)) (1253105663 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((67090177741 / 500000) : ℝ) ≤ Real.exp (3 * (3935647 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3935647 / 1000000)) (67090177741 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1803 / 16000) : ℝ) (361 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3935647 / 1000000) (3936757 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1803 / 16000) (361 / 3200) (50111697 / 40000000) (1253105663 / 1000000000) (3935647 / 1000000) (3936757 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1803 / 16000) (361 / 3200) (3935647 / 1000000) (3936757 / 1000000) (4792 / 125) (38379 / 1000)
    (10222 / 125) (82469 / 1000) (-287473 / 500) (233739 / 1000000) (960759 / 250) (47697 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3935647 / 1000000) (67090177741 / 500000) (47697 / 25000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3935647 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3935647 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell112 :
    ∀ t ∈ Set.Icc ((361 / 3200) : ℝ) (1807 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((626552831 / 500000000) : ℝ) ≤ Real.exp (2 * (361 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (361 / 3200)) (626552831 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1807 / 16000) : ℝ)) ≤ (1253418979 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1807 / 16000)) (1253418979 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((13457704049 / 100000) : ℝ) ≤ Real.exp (3 * (3936631 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3936631 / 1000000)) (13457704049 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((361 / 3200) : ℝ) (1807 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3936631 / 1000000) (1968871 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (361 / 3200) (1807 / 16000) (626552831 / 500000000) (1253418979 / 1000000000) (3936631 / 1000000) (1968871 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (361 / 3200) (1807 / 16000) (3936631 / 1000000) (1968871 / 500000) (38361 / 1000) (9601 / 250)
    (20481 / 250) (41309 / 500) (-287489 / 500) (9329 / 40000) (961721 / 250) (1902257 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3936631 / 1000000) (13457704049 / 100000) (1902257 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3936631 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3936631 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell113 :
    ∀ t ∈ Set.Icc ((1807 / 16000) : ℝ) (1809 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((626709489 / 500000000) : ℝ) ≤ Real.exp (2 * (1807 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1807 / 16000)) (626709489 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1809 / 16000) : ℝ)) ≤ (1253732373 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1809 / 16000)) (1253732373 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((134974898237 / 1000000) : ℝ) ≤ Real.exp (3 * (787523 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (787523 / 200000)) (134974898237 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1807 / 16000) : ℝ) (1809 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (787523 / 200000) (1969363 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1807 / 16000) (1809 / 16000) (626709489 / 500000000) (1253732373 / 1000000000) (787523 / 200000) (1969363 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1807 / 16000) (1809 / 16000) (787523 / 200000) (1969363 / 500000) (19193 / 500) (38429 / 1000)
    (82073 / 1000) (41383 / 500) (-287507 / 500) (29089 / 125000) (385073 / 100) (1896649 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (787523 / 200000) (134974898237 / 1000000) (1896649 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (787523 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (787523 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell114 :
    ∀ t ∈ Set.Icc ((1809 / 16000) : ℝ) (1811 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((313433093 / 250000000) : ℝ) ≤ Real.exp (2 * (1809 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1809 / 16000)) (313433093 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1811 / 16000) : ℝ)) ≤ (250809169 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1811 / 16000)) (250809169 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16921792289 / 125000) : ℝ) ≤ Real.exp (3 * (19693 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (19693 / 5000)) (16921792289 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1809 / 16000) : ℝ) (1811 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (19693 / 5000) (3939711 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1809 / 16000) (1811 / 16000) (313433093 / 250000000) (250809169 / 200000000) (19693 / 5000) (3939711 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1809 / 16000) (1811 / 16000) (19693 / 5000) (3939711 / 1000000) (9603 / 250) (19227 / 500)
    (82221 / 1000) (16583 / 200) (-11501 / 20) (1161 / 5000) (481823 / 125) (1891053 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (19693 / 5000) (16921792289 / 125000) (1891053 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (19693 / 5000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (19693 / 5000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell115 :
    ∀ t ∈ Set.Icc ((1811 / 16000) : ℝ) (1813 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((313511461 / 250000000) : ℝ) ≤ Real.exp (2 * (1811 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1811 / 16000)) (313511461 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1813 / 16000) : ℝ)) ≤ (250871879 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1813 / 16000)) (250871879 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((135774960473 / 1000000) : ℝ) ≤ Real.exp (3 * (787917 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (787917 / 200000)) (135774960473 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1811 / 16000) : ℝ) (1813 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (787917 / 200000) (492587 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1811 / 16000) (1813 / 16000) (313511461 / 250000000) (250871879 / 200000000) (787917 / 200000) (492587 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1811 / 16000) (1813 / 16000) (787917 / 200000) (492587 / 125000) (38437 / 1000) (38479 / 1000)
    (8237 / 100) (10383 / 125) (-115017 / 200) (28961 / 125000) (96461 / 25) (1885473 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (787917 / 200000) (135774960473 / 1000000) (1885473 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (787917 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (787917 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell116 :
    ∀ t ∈ Set.Icc ((1813 / 16000) : ℝ) (363 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((627179697 / 500000000) : ℝ) ≤ Real.exp (2 * (1813 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1813 / 16000)) (627179697 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((363 / 3200) : ℝ)) ≤ (50186921 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (363 / 3200)) (50186921 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((68088384109 / 500000) : ℝ) ≤ Real.exp (3 * (394057 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (394057 / 100000)) (68088384109 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1813 / 16000) : ℝ) (363 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (394057 / 100000) (3941681 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1813 / 16000) (363 / 3200) (627179697 / 500000000) (50186921 / 40000000) (394057 / 100000) (3941681 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1813 / 16000) (363 / 3200) (394057 / 100000) (3941681 / 1000000) (19231 / 500) (4813 / 125)
    (82519 / 1000) (83213 / 1000) (-14378 / 25) (115589 / 500000) (3862299 / 1000) (187991 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (394057 / 100000) (68088384109 / 500000) (187991 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (394057 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (394057 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell117 :
    ∀ t ∈ Set.Icc ((363 / 3200) : ℝ) (1817 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((9802133 / 7812500) : ℝ) ≤ Real.exp (2 * (363 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (363 / 3200)) (9802133 / 7812500) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1817 / 16000) : ℝ)) ≤ (313746683 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1817 / 16000)) (313746683 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((136579765057 / 1000000) : ℝ) ≤ Real.exp (3 * (788311 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (788311 / 200000)) (136579765057 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((363 / 3200) : ℝ) (1817 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (788311 / 200000) (3942667 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (363 / 3200) (1817 / 16000) (9802133 / 7812500) (313746683 / 250000000) (788311 / 200000) (3942667 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (363 / 3200) (1817 / 16000) (788311 / 200000) (3942667 / 1000000) (38487 / 1000) (3853 / 100)
    (20667 / 250) (83363 / 1000) (-143787 / 250) (230669 / 1000000) (773233 / 200) (1874363 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (788311 / 200000) (136579765057 / 1000000) (1874363 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (788311 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (788311 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell118 :
    ∀ t ∈ Set.Icc ((1817 / 16000) : ℝ) (1819 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1254986731 / 1000000000) : ℝ) ≤ Real.exp (2 * (1817 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1817 / 16000)) (1254986731 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1819 / 16000) : ℝ)) ≤ (627650259 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1819 / 16000)) (627650259 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((136983954507 / 1000000) : ℝ) ≤ Real.exp (3 * (197127 / 50000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (197127 / 50000)) (136983954507 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1817 / 16000) : ℝ) (1819 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (197127 / 50000) (3943653 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1817 / 16000) (1819 / 16000) (1254986731 / 1000000000) (627650259 / 500000000) (197127 / 50000) (3943653 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1817 / 16000) (1819 / 16000) (197127 / 50000) (3943653 / 1000000) (4814 / 125) (7711 / 200)
    (10352 / 125) (83513 / 1000) (-71897 / 125) (230161 / 1000000) (1935017 / 500) (1868833 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (197127 / 50000) (136983954507 / 1000000) (1868833 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (197127 / 50000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (197127 / 50000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell119 :
    ∀ t ∈ Set.Icc ((1819 / 16000) : ℝ) (1821 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1255300517 / 1000000000) : ℝ) ≤ Real.exp (2 * (1819 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1819 / 16000)) (1255300517 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1821 / 16000) : ℝ)) ≤ (627807191 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1821 / 16000)) (627807191 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((137389752267 / 1000000) : ℝ) ≤ Real.exp (3 * (1971763 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1971763 / 500000)) (137389752267 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1819 / 16000) : ℝ) (1821 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1971763 / 500000) (3944639 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1819 / 16000) (1821 / 16000) (1255300517 / 1000000000) (627807191 / 500000000) (1971763 / 500000) (3944639 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1819 / 16000) (1821 / 16000) (1971763 / 500000) (3944639 / 1000000) (38537 / 1000) (1929 / 50)
    (41483 / 500) (41831 / 500) (-575209 / 1000) (229653 / 1000000) (1936953 / 500) (1863313 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1971763 / 500000) (137389752267 / 1000000) (1863313 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1971763 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1971763 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityExpCompact_cellsBatch005 :
    ∀ t ∈ Set.Icc ((1781 / 16000) : ℝ) (1821 / 16000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell100
      hpThetaDensityExpCompact_cell101)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell102
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell103
      hpThetaDensityExpCompact_cell104)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell105
      hpThetaDensityExpCompact_cell106)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell107
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell108
      hpThetaDensityExpCompact_cell109))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell110
      hpThetaDensityExpCompact_cell111)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell112
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell113
      hpThetaDensityExpCompact_cell114)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell115
      hpThetaDensityExpCompact_cell116)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell117
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell118
      hpThetaDensityExpCompact_cell119)))))

#print axioms hpThetaDensityExpCompact_cellsBatch005
end HodgeProofHP
