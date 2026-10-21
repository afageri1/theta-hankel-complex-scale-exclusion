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
theorem hpThetaDensityLowerExpCompact_cell100 :
    ∀ t ∈ Set.Icc ((2053 / 25600) : ℝ) (41061 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173969363 / 1000000000) : ℝ) ≤ Real.exp (2 * (2053 / 25600)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2053 / 25600)) (1173969363 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41061 / 512000) : ℝ)) ≤ (23479479 / 20000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41061 / 512000)) (23479479 / 20000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63835948953 / 1000000) : ℝ) ≤ Real.exp (3 * (461003 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (461003 / 125000)) (63835948953 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2053 / 25600) : ℝ) (41061 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (461003 / 125000) (3688157 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2053 / 25600) (41061 / 512000) (1173969363 / 1000000000) (23479479 / 20000000) (461003 / 125000) (3688157 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2053 / 25600) (41061 / 512000) (461003 / 125000) (3688157 / 1000000) (32277 / 1000) (16141 / 500)
    (48547 / 1000) (48623 / 1000) (-110333 / 200) (403987 / 1000000) (2960449 / 1000) (100257 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (461003 / 125000) (63835948953 / 1000000) (100257 / 25000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461003 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461003 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell101 :
    ∀ t ∈ Set.Icc ((41061 / 512000) : ℝ) (20531 / 256000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1173973949 / 1000000000) : ℝ) ≤ Real.exp (2 * (41061 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41061 / 512000)) (1173973949 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((20531 / 256000) : ℝ)) ≤ (234795707 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (20531 / 256000)) (234795707 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31919410817 / 500000) : ℝ) ≤ Real.exp (3 * (3688039 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3688039 / 1000000)) (31919410817 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41061 / 512000) : ℝ) (20531 / 256000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3688039 / 1000000) (3688171 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41061 / 512000) (20531 / 256000) (1173973949 / 1000000000) (234795707 / 200000000) (3688039 / 1000000) (3688171 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41061 / 512000) (20531 / 256000) (3688039 / 1000000) (3688171 / 1000000) (32277 / 1000) (32283 / 1000)
    (48549 / 1000) (6078 / 125) (-68959 / 125) (403973 / 1000000) (1480247 / 500) (40101 / 10000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3688039 / 1000000) (31919410817 / 500000) (40101 / 10000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688039 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688039 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell102 :
    ∀ t ∈ Set.Icc ((20531 / 256000) : ℝ) (41063 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((586989267 / 500000000) : ℝ) ≤ Real.exp (2 * (20531 / 256000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (20531 / 256000)) (586989267 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41063 / 512000) : ℝ)) ≤ (1173983121 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41063 / 512000)) (1173983121 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63841502919 / 1000000) : ℝ) ≤ Real.exp (3 * (3688053 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3688053 / 1000000)) (63841502919 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((20531 / 256000) : ℝ) (41063 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3688053 / 1000000) (1844093 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (20531 / 256000) (41063 / 512000) (586989267 / 500000000) (1173983121 / 1000000000) (3688053 / 1000000) (1844093 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (20531 / 256000) (41063 / 512000) (3688053 / 1000000) (1844093 / 500000) (32277 / 1000) (32283 / 1000)
    (971 / 20) (24313 / 500) (-55167 / 100) (403961 / 1000000) (2960543 / 1000) (4009931 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3688053 / 1000000) (63841502919 / 1000000) (4009931 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688053 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688053 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell103 :
    ∀ t ∈ Set.Icc ((41063 / 512000) : ℝ) (5133 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((14674789 / 12500000) : ℝ) ≤ Real.exp (2 * (41063 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41063 / 512000)) (14674789 / 12500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((5133 / 64000) : ℝ)) ≤ (1173987707 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (5133 / 64000)) (1173987707 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31922092159 / 500000) : ℝ) ≤ Real.exp (3 * (3688067 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3688067 / 1000000)) (31922092159 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41063 / 512000) : ℝ) (5133 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3688067 / 1000000) (18441 / 5000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41063 / 512000) (5133 / 64000) (14674789 / 12500000) (1173987707 / 1000000000) (3688067 / 1000000) (18441 / 5000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41063 / 512000) (5133 / 64000) (3688067 / 1000000) (18441 / 5000) (16139 / 500) (32283 / 1000)
    (6069 / 125) (12157 / 250) (-551673 / 1000) (403949 / 1000000) (740147 / 250) (4009763 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3688067 / 1000000) (31922092159 / 500000) (4009763 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688067 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688067 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell104 :
    ∀ t ∈ Set.Icc ((5133 / 64000) : ℝ) (8213 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((586993853 / 500000000) : ℝ) ≤ Real.exp (2 * (5133 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (5133 / 64000)) (586993853 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8213 / 102400) : ℝ)) ≤ (1173992293 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8213 / 102400)) (1173992293 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63847057369 / 1000000) : ℝ) ≤ Real.exp (3 * (1844041 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1844041 / 500000)) (63847057369 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((5133 / 64000) : ℝ) (8213 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1844041 / 500000) (737643 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (5133 / 64000) (8213 / 102400) (586993853 / 500000000) (1173992293 / 1000000000) (1844041 / 500000) (737643 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (5133 / 64000) (8213 / 102400) (1844041 / 500000) (737643 / 200000) (16139 / 500) (8071 / 250)
    (24277 / 500) (4863 / 100) (-22067 / 40) (12623 / 31250) (740159 / 250) (2004791 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1844041 / 500000) (63847057369 / 1000000) (2004791 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844041 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844041 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell105 :
    ∀ t ∈ Set.Icc ((8213 / 102400) : ℝ) (20533 / 256000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((293498073 / 250000000) : ℝ) ≤ Real.exp (2 * (8213 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8213 / 102400)) (293498073 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((20533 / 256000) : ℝ)) ≤ (1173996879 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (20533 / 256000)) (1173996879 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63849739001 / 1000000) : ℝ) ≤ Real.exp (3 * (115253 / 31250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (115253 / 31250)) (63849739001 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8213 / 102400) : ℝ) (20533 / 256000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (115253 / 31250) (3688229 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8213 / 102400) (20533 / 256000) (293498073 / 250000000) (1173996879 / 1000000000) (115253 / 31250) (3688229 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8213 / 102400) (20533 / 256000) (115253 / 31250) (3688229 / 1000000) (16139 / 500) (8071 / 250)
    (9711 / 200) (48631 / 1000) (-275839 / 500) (403923 / 1000000) (2960681 / 1000) (2004707 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (115253 / 31250) (63849739001 / 1000000) (2004707 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (115253 / 31250)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (115253 / 31250)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell106 :
    ∀ t ∈ Set.Icc ((20533 / 256000) : ℝ) (41067 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((586998439 / 500000000) : ℝ) ≤ Real.exp (2 * (20533 / 256000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (20533 / 256000)) (586998439 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41067 / 512000) : ℝ)) ≤ (234800293 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41067 / 512000)) (234800293 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63852612303 / 1000000) : ℝ) ≤ Real.exp (3 * (3688111 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3688111 / 1000000)) (63852612303 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((20533 / 256000) : ℝ) (41067 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3688111 / 1000000) (922061 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (20533 / 256000) (41067 / 512000) (586998439 / 500000000) (234800293 / 200000000) (3688111 / 1000000) (922061 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (20533 / 256000) (41067 / 512000) (3688111 / 1000000) (922061 / 250000) (32279 / 1000) (8071 / 250)
    (48557 / 1000) (48633 / 1000) (-551681 / 1000) (40391 / 100000) (2960729 / 1000) (4009233 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3688111 / 1000000) (63852612303 / 1000000) (4009233 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688111 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688111 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell107 :
    ∀ t ∈ Set.Icc ((41067 / 512000) : ℝ) (10267 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((146750183 / 125000000) : ℝ) ≤ Real.exp (2 * (41067 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41067 / 512000)) (146750183 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((10267 / 128000) : ℝ)) ≤ (1174006051 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (10267 / 128000)) (1174006051 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63855294167 / 1000000) : ℝ) ≤ Real.exp (3 * (5901 / 1600)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5901 / 1600)) (63855294167 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41067 / 512000) : ℝ) (10267 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5901 / 1600) (1844129 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41067 / 512000) (10267 / 128000) (146750183 / 125000000) (1174006051 / 1000000000) (5901 / 1600) (1844129 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41067 / 512000) (10267 / 128000) (5901 / 1600) (1844129 / 500000) (32279 / 1000) (6457 / 200)
    (48559 / 1000) (9727 / 200) (-551683 / 1000) (201949 / 500000) (1480387 / 500) (801813 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5901 / 1600) (63855294167 / 1000000) (801813 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5901 / 1600)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5901 / 1600)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell108 :
    ∀ t ∈ Set.Icc ((10267 / 128000) : ℝ) (41069 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((23480121 / 20000000) : ℝ) ≤ Real.exp (2 * (10267 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (10267 / 128000)) (23480121 / 20000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41069 / 512000) : ℝ)) ≤ (1174010637 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41069 / 512000)) (1174010637 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63858167719 / 1000000) : ℝ) ≤ Real.exp (3 * (184407 / 50000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (184407 / 50000)) (63858167719 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((10267 / 128000) : ℝ) (41069 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (184407 / 50000) (230517 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (10267 / 128000) (41069 / 512000) (23480121 / 20000000) (1174010637 / 1000000000) (184407 / 50000) (230517 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (10267 / 128000) (41069 / 512000) (184407 / 50000) (230517 / 62500) (32279 / 1000) (6457 / 200)
    (48561 / 1000) (12159 / 250) (-55169 / 100) (100971 / 250000) (2960819 / 1000) (801777 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (184407 / 50000) (63858167719 / 1000000) (801777 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (184407 / 50000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (184407 / 50000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell109 :
    ∀ t ∈ Set.Icc ((41069 / 512000) : ℝ) (4107 / 51200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((293502659 / 250000000) : ℝ) ≤ Real.exp (2 * (41069 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41069 / 512000)) (293502659 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4107 / 51200) : ℝ)) ≤ (1174015223 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4107 / 51200)) (1174015223 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63860849817 / 1000000) : ℝ) ≤ Real.exp (3 * (1844077 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1844077 / 500000)) (63860849817 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41069 / 512000) : ℝ) (4107 / 51200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1844077 / 500000) (3688287 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41069 / 512000) (4107 / 51200) (293502659 / 250000000) (1174015223 / 1000000000) (1844077 / 500000) (3688287 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41069 / 512000) (4107 / 51200) (1844077 / 500000) (3688287 / 1000000) (807 / 25) (6457 / 200)
    (24281 / 500) (24319 / 500) (-68961 / 125) (12621 / 31250) (2960867 / 1000) (1002179 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1844077 / 500000) (63860849817 / 1000000) (1002179 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844077 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844077 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell110 :
    ∀ t ∈ Set.Icc ((4107 / 51200) : ℝ) (41071 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587007611 / 500000000) : ℝ) ≤ Real.exp (2 * (4107 / 51200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4107 / 51200)) (587007611 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41071 / 512000) : ℝ)) ≤ (1174019809 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41071 / 512000)) (1174019809 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((15965883007 / 250000) : ℝ) ≤ Real.exp (3 * (461021 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (461021 / 125000)) (15965883007 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4107 / 51200) : ℝ) (41071 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (461021 / 125000) (3688301 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (4107 / 51200) (41071 / 512000) (587007611 / 500000000) (1174019809 / 1000000000) (461021 / 125000) (3688301 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (4107 / 51200) (41071 / 512000) (461021 / 125000) (3688301 / 1000000) (807 / 25) (16143 / 500)
    (12141 / 250) (1216 / 25) (-551691 / 1000) (20193 / 50000) (370114 / 125) (1002137 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (461021 / 125000) (15965883007 / 250000) (1002137 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461021 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461021 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell111 :
    ∀ t ∈ Set.Icc ((41071 / 512000) : ℝ) (2567 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((36688119 / 31250000) : ℝ) ≤ Real.exp (2 * (41071 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41071 / 512000)) (36688119 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2567 / 32000) : ℝ)) ≤ (234804879 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2567 / 32000)) (234804879 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1277328119 / 20000) : ℝ) ≤ Real.exp (3 * (3688183 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3688183 / 1000000)) (1277328119 / 20000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41071 / 512000) : ℝ) (2567 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3688183 / 1000000) (922079 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41071 / 512000) (2567 / 32000) (36688119 / 31250000) (234804879 / 200000000) (3688183 / 1000000) (922079 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41071 / 512000) (2567 / 32000) (3688183 / 1000000) (922079 / 250000) (807 / 25) (16143 / 500)
    (24283 / 500) (24321 / 500) (-275847 / 500) (201923 / 500000) (74024 / 25) (250523 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3688183 / 1000000) (1277328119 / 20000) (250523 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688183 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688183 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell112 :
    ∀ t ∈ Set.Icc ((2567 / 32000) : ℝ) (41073 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587012197 / 500000000) : ℝ) ≤ Real.exp (2 * (2567 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2567 / 32000)) (587012197 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41073 / 512000) : ℝ)) ≤ (1174028981 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41073 / 512000)) (1174028981 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((12773817679 / 200000) : ℝ) ≤ Real.exp (3 * (3688197 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3688197 / 1000000)) (12773817679 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2567 / 32000) : ℝ) (41073 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3688197 / 1000000) (368833 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2567 / 32000) (41073 / 512000) (587012197 / 500000000) (1174028981 / 1000000000) (3688197 / 1000000) (368833 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2567 / 32000) (41073 / 512000) (3688197 / 1000000) (368833 / 100000) (32281 / 1000) (16143 / 500)
    (48567 / 1000) (48643 / 1000) (-68962 / 125) (201917 / 500000) (592201 / 200) (4008199 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3688197 / 1000000) (12773817679 / 200000) (4008199 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688197 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688197 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell113 :
    ∀ t ∈ Set.Icc ((41073 / 512000) : ℝ) (20537 / 256000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((58701449 / 50000000) : ℝ) ≤ Real.exp (2 * (41073 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41073 / 512000)) (58701449 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((20537 / 256000) : ℝ)) ≤ (1174033567 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (20537 / 256000)) (1174033567 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63871962567 / 1000000) : ℝ) ≤ Real.exp (3 * (922053 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (922053 / 250000)) (63871962567 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41073 / 512000) : ℝ) (20537 / 256000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (922053 / 250000) (461043 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41073 / 512000) (20537 / 256000) (58701449 / 50000000) (1174033567 / 1000000000) (922053 / 250000) (461043 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41073 / 512000) (20537 / 256000) (922053 / 250000) (461043 / 125000) (32281 / 1000) (32287 / 1000)
    (48569 / 1000) (9729 / 200) (-551703 / 1000) (20191 / 50000) (59221 / 20) (4008019 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (922053 / 250000) (63871962567 / 1000000) (4008019 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922053 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922053 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell114 :
    ∀ t ∈ Set.Icc ((20537 / 256000) : ℝ) (1643 / 20480), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587016783 / 500000000) : ℝ) ≤ Real.exp (2 * (20537 / 256000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (20537 / 256000)) (587016783 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1643 / 20480) : ℝ)) ≤ (1174038153 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1643 / 20480)) (1174038153 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((12774929049 / 200000) : ℝ) ≤ Real.exp (3 * (1844113 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1844113 / 500000)) (12774929049 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((20537 / 256000) : ℝ) (1643 / 20480),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1844113 / 500000) (3688359 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (20537 / 256000) (1643 / 20480) (587016783 / 500000000) (1174038153 / 1000000000) (1844113 / 500000) (3688359 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (20537 / 256000) (1643 / 20480) (1844113 / 500000) (3688359 / 1000000) (32281 / 1000) (32287 / 1000)
    (48571 / 1000) (48647 / 1000) (-551701 / 1000) (12619 / 31250) (1480549 / 500) (4007851 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1844113 / 500000) (12774929049 / 200000) (4007851 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844113 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844113 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell115 :
    ∀ t ∈ Set.Icc ((1643 / 20480) : ℝ) (10269 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((146754769 / 125000000) : ℝ) ≤ Real.exp (2 * (1643 / 20480)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1643 / 20480)) (146754769 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((10269 / 128000) : ℝ)) ≤ (1174042739 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (10269 / 128000)) (1174042739 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((12775465607 / 200000) : ℝ) ≤ Real.exp (3 * (46103 / 12500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (46103 / 12500)) (12775465607 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1643 / 20480) : ℝ) (10269 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (46103 / 12500) (3688373 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1643 / 20480) (10269 / 128000) (146754769 / 125000000) (1174042739 / 1000000000) (46103 / 12500) (3688373 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1643 / 20480) (10269 / 128000) (46103 / 12500) (3688373 / 1000000) (16141 / 500) (32287 / 1000)
    (48573 / 1000) (6081 / 125) (-68963 / 125) (100949 / 250000) (2961143 / 1000) (2003841 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (46103 / 12500) (12775465607 / 200000) (2003841 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (46103 / 12500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (46103 / 12500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell116 :
    ∀ t ∈ Set.Icc ((10269 / 128000) : ℝ) (41077 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587021369 / 500000000) : ℝ) ≤ Real.exp (2 * (10269 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (10269 / 128000)) (587021369 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41077 / 512000) : ℝ)) ≤ (46961893 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41077 / 512000)) (46961893 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31940101289 / 500000) : ℝ) ≤ Real.exp (3 * (737651 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (737651 / 200000)) (31940101289 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((10269 / 128000) : ℝ) (41077 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (737651 / 200000) (922097 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (10269 / 128000) (41077 / 512000) (587021369 / 500000000) (46961893 / 40000000) (737651 / 200000) (922097 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (10269 / 128000) (41077 / 512000) (737651 / 200000) (922097 / 250000) (16141 / 500) (4036 / 125)
    (24287 / 500) (973 / 20) (-551707 / 1000) (403783 / 1000000) (2961191 / 1000) (2003751 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (737651 / 200000) (31940101289 / 500000) (2003751 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (737651 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (737651 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell117 :
    ∀ t ∈ Set.Icc ((41077 / 512000) : ℝ) (20539 / 256000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((293511831 / 250000000) : ℝ) ≤ Real.exp (2 * (41077 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41077 / 512000)) (293511831 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((20539 / 256000) : ℝ)) ≤ (1174051911 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (20539 / 256000)) (1174051911 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31941442801 / 500000) : ℝ) ≤ Real.exp (3 * (3688269 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3688269 / 1000000)) (31941442801 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41077 / 512000) : ℝ) (20539 / 256000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3688269 / 1000000) (1844201 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41077 / 512000) (20539 / 256000) (293511831 / 250000000) (1174051911 / 1000000000) (3688269 / 1000000) (1844201 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41077 / 512000) (20539 / 256000) (3688269 / 1000000) (1844201 / 500000) (16141 / 500) (4036 / 125)
    (6072 / 125) (12163 / 250) (-551709 / 1000) (40377 / 100000) (740309 / 250) (2003667 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3688269 / 1000000) (31941442801 / 500000) (2003667 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688269 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688269 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell118 :
    ∀ t ∈ Set.Icc ((20539 / 256000) : ℝ) (41079 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((117405191 / 100000000) : ℝ) ≤ Real.exp (2 * (20539 / 256000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (20539 / 256000)) (117405191 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41079 / 512000) : ℝ)) ≤ (1174056497 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41079 / 512000)) (1174056497 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((12777152079 / 200000) : ℝ) ≤ Real.exp (3 * (922071 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (922071 / 250000)) (12777152079 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((20539 / 256000) : ℝ) (41079 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (922071 / 250000) (115263 / 31250) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (20539 / 256000) (41079 / 512000) (117405191 / 100000000) (1174056497 / 1000000000) (922071 / 250000) (115263 / 31250) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (20539 / 256000) (41079 / 512000) (922071 / 250000) (115263 / 31250) (32283 / 1000) (4036 / 125)
    (24289 / 500) (48653 / 1000) (-137929 / 250) (403757 / 1000000) (2961281 / 1000) (4007153 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (922071 / 250000) (12777152079 / 200000) (4007153 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922071 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922071 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell119 :
    ∀ t ∈ Set.Icc ((41079 / 512000) : ℝ) (1027 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((73378531 / 62500000) : ℝ) ≤ Real.exp (2 * (41079 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41079 / 512000)) (73378531 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1027 / 12800) : ℝ)) ≤ (293515271 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1027 / 12800)) (293515271 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((15972110913 / 250000) : ℝ) ≤ Real.exp (3 * (1844149 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1844149 / 500000)) (15972110913 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41079 / 512000) : ℝ) (1027 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1844149 / 500000) (3688431 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41079 / 512000) (1027 / 12800) (73378531 / 62500000) (293515271 / 250000000) (1844149 / 500000) (3688431 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41079 / 512000) (1027 / 12800) (1844149 / 500000) (3688431 / 1000000) (32283 / 1000) (32289 / 1000)
    (2429 / 50) (9731 / 200) (-275857 / 500) (80749 / 200000) (2961329 / 1000) (801397 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1844149 / 500000) (15972110913 / 250000) (801397 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844149 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844149 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch005 :
    ∀ t ∈ Set.Icc ((2053 / 25600) : ℝ) (1027 / 12800),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell100
      hpThetaDensityLowerExpCompact_cell101)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell102
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell103
      hpThetaDensityLowerExpCompact_cell104)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell105
      hpThetaDensityLowerExpCompact_cell106)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell107
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell108
      hpThetaDensityLowerExpCompact_cell109))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell110
      hpThetaDensityLowerExpCompact_cell111)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell112
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell113
      hpThetaDensityLowerExpCompact_cell114)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell115
      hpThetaDensityLowerExpCompact_cell116)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell117
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell118
      hpThetaDensityLowerExpCompact_cell119)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch005
end HodgeProofHP
