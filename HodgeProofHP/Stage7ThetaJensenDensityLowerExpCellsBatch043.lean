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
theorem hpThetaDensityLowerExpCompact_cell860 :
    ∀ t ∈ Set.Icc ((46307 / 512000) : ℝ) (46323 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1198279429 / 1000000000) : ℝ) ≤ Real.exp (2 * (46307 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46307 / 512000)) (1198279429 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46323 / 512000) : ℝ)) ≤ (299588581 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46323 / 512000)) (299588581 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((80272441759 / 1000000) : ℝ) ≤ Real.exp (3 * (1882197 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1882197 / 500000)) (80272441759 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46307 / 512000) : ℝ) (46323 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1882197 / 500000) (15059 / 4000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46307 / 512000) (46323 / 512000) (1198279429 / 1000000000) (299588581 / 250000000) (1882197 / 500000) (15059 / 4000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46307 / 512000) (46323 / 512000) (1882197 / 500000) (15059 / 4000) (17047 / 500) (8527 / 250)
    (58017 / 1000) (2329 / 40) (-140737 / 250) (341701 / 1000000) (3214139 / 1000) (159457 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1882197 / 500000) (80272441759 / 1000000) (159457 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1882197 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1882197 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell861 :
    ∀ t ∈ Set.Icc ((46323 / 512000) : ℝ) (46339 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1198354323 / 1000000000) : ℝ) ≤ Real.exp (2 * (46323 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46323 / 512000)) (1198354323 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46339 / 512000) : ℝ)) ≤ (149803653 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46339 / 512000)) (149803653 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((80329294733 / 1000000) : ℝ) ≤ Real.exp (3 * (376463 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (376463 / 100000)) (80329294733 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46323 / 512000) : ℝ) (46339 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (376463 / 100000) (1882493 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46323 / 512000) (46339 / 512000) (1198354323 / 1000000000) (149803653 / 125000000) (376463 / 100000) (1882493 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46323 / 512000) (46339 / 512000) (376463 / 100000) (1882493 / 500000) (34099 / 1000) (34113 / 1000)
    (58047 / 1000) (11651 / 200) (-562981 / 1000) (341523 / 1000000) (642989 / 200) (3186883 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (376463 / 100000) (80329294733 / 1000000) (3186883 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (376463 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (376463 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell862 :
    ∀ t ∈ Set.Icc ((46339 / 512000) : ℝ) (9271 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1198429223 / 1000000000) : ℝ) ≤ Real.exp (2 * (46339 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46339 / 512000)) (1198429223 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9271 / 102400) : ℝ)) ≤ (18726627 / 15625000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9271 / 102400)) (18726627 / 15625000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1256030419 / 15625) : ℝ) ≤ Real.exp (3 * (752973 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (752973 / 200000)) (1256030419 / 15625) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46339 / 512000) : ℝ) (9271 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (752973 / 200000) (3765221 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46339 / 512000) (9271 / 102400) (1198429223 / 1000000000) (18726627 / 15625000) (752973 / 200000) (3765221 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46339 / 512000) (9271 / 102400) (752973 / 200000) (3765221 / 1000000) (6821 / 200) (34119 / 1000)
    (29039 / 500) (29143 / 500) (-281507 / 500) (341347 / 1000000) (3215747 / 1000) (3184637 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (752973 / 200000) (1256030419 / 15625) (3184637 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (752973 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (752973 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell863 :
    ∀ t ∈ Set.Icc ((9271 / 102400) : ℝ) (46371 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1198504127 / 1000000000) : ℝ) ≤ Real.exp (2 * (9271 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9271 / 102400)) (1198504127 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46371 / 512000) : ℝ)) ≤ (1198579037 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46371 / 512000)) (1198579037 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((80442638853 / 1000000) : ℝ) ≤ Real.exp (3 * (37651 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (37651 / 10000)) (80442638853 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9271 / 102400) : ℝ) (46371 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (37651 / 10000) (235341 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (9271 / 102400) (46371 / 512000) (1198504127 / 1000000000) (1198579037 / 1000000000) (37651 / 10000) (235341 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (9271 / 102400) (46371 / 512000) (37651 / 10000) (235341 / 62500) (34111 / 1000) (273 / 8)
    (14527 / 250) (14579 / 250) (-563047 / 1000) (34117 / 100000) (64331 / 20) (397799 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (37651 / 10000) (80442638853 / 1000000) (397799 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (37651 / 10000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (37651 / 10000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell864 :
    ∀ t ∈ Set.Icc ((46371 / 512000) : ℝ) (46387 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((299644759 / 250000000) : ℝ) ≤ Real.exp (2 * (46371 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46371 / 512000)) (299644759 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46387 / 512000) : ℝ)) ≤ (23973079 / 20000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46387 / 512000)) (23973079 / 20000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8049961237 / 100000) : ℝ) ≤ Real.exp (3 * (470667 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (470667 / 125000)) (8049961237 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46371 / 512000) : ℝ) (46387 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (470667 / 125000) (941423 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46371 / 512000) (46387 / 512000) (299644759 / 250000000) (23973079 / 20000000) (470667 / 125000) (941423 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46371 / 512000) (46387 / 512000) (470667 / 125000) (941423 / 250000) (8529 / 250) (3413 / 100)
    (58139 / 1000) (29173 / 500) (-563081 / 1000) (340993 / 1000000) (3217357 / 1000) (159007 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (470667 / 125000) (8049961237 / 100000) (159007 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (470667 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (470667 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell865 :
    ∀ t ∈ Set.Icc ((46387 / 512000) : ℝ) (46419 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1198653949 / 1000000000) : ℝ) ≤ Real.exp (2 * (46387 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46387 / 512000)) (1198653949 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46419 / 512000) : ℝ)) ≤ (1198803791 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46419 / 512000)) (1198803791 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((80556384569 / 1000000) : ℝ) ≤ Real.exp (3 * (3765571 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3765571 / 1000000)) (80556384569 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46387 / 512000) : ℝ) (46419 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3765571 / 1000000) (1883081 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46387 / 512000) (46419 / 512000) (1198653949 / 1000000000) (1198803791 / 1000000000) (3765571 / 1000000) (1883081 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46387 / 512000) (46419 / 512000) (3765571 / 1000000) (1883081 / 500000) (34121 / 1000) (34143 / 1000)
    (14529 / 250) (2923 / 50) (-281009 / 500) (4261 / 12500) (3218963 / 1000) (3177899 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3765571 / 1000000) (80556384569 / 1000000) (3177899 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3765571 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3765571 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell866 :
    ∀ t ∈ Set.Icc ((46419 / 512000) : ℝ) (46451 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((119880379 / 100000000) : ℝ) ≤ Real.exp (2 * (46419 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46419 / 512000)) (119880379 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46451 / 512000) : ℝ)) ≤ (1198953651 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46451 / 512000)) (1198953651 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((80670291121 / 1000000) : ℝ) ≤ Real.exp (3 * (1883021 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1883021 / 500000)) (80670291121 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46419 / 512000) : ℝ) (46451 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1883021 / 500000) (3766633 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46419 / 512000) (46451 / 512000) (119880379 / 100000000) (1198953651 / 1000000000) (1883021 / 500000) (3766633 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46419 / 512000) (46451 / 512000) (1883021 / 500000) (3766633 / 1000000) (8533 / 250) (17077 / 500)
    (58177 / 1000) (58521 / 1000) (-140521 / 250) (170263 / 500000) (1610287 / 500) (793353 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1883021 / 500000) (80670291121 / 1000000) (793353 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1883021 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1883021 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell867 :
    ∀ t ∈ Set.Icc ((46451 / 512000) : ℝ) (46483 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((23979073 / 20000000) : ℝ) ≤ Real.exp (2 * (46451 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46451 / 512000)) (23979073 / 20000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46483 / 512000) : ℝ)) ≤ (119910353 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46483 / 512000)) (119910353 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2524503637 / 31250) : ℝ) ≤ Real.exp (3 * (235407 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (235407 / 62500)) (2524503637 / 31250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46451 / 512000) : ℝ) (46483 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (235407 / 62500) (58861 / 15625) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46451 / 512000) (46483 / 512000) (23979073 / 20000000) (119910353 / 100000000) (235407 / 62500) (58861 / 15625) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46451 / 512000) (46483 / 512000) (235407 / 62500) (58861 / 15625) (34143 / 1000) (17083 / 500)
    (58237 / 1000) (58583 / 1000) (-112429 / 200) (170087 / 500000) (644437 / 200) (158447 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (235407 / 62500) (2524503637 / 31250) (158447 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (235407 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (235407 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell868 :
    ∀ t ∈ Set.Icc ((46483 / 512000) : ℝ) (9303 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1199103529 / 1000000000) : ℝ) ≤ Real.exp (2 * (46483 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46483 / 512000)) (1199103529 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9303 / 102400) : ℝ)) ≤ (1199253427 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9303 / 102400)) (1199253427 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((20224586237 / 250000) : ℝ) ≤ Real.exp (3 * (3766983 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3766983 / 1000000)) (20224586237 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46483 / 512000) : ℝ) (9303 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3766983 / 1000000) (150703 / 40000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46483 / 512000) (9303 / 102400) (1199103529 / 1000000000) (1199253427 / 1000000000) (3766983 / 1000000) (150703 / 40000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46483 / 512000) (9303 / 102400) (3766983 / 1000000) (150703 / 40000) (6831 / 200) (34177 / 1000)
    (29149 / 500) (14661 / 250) (-562211 / 1000) (339821 / 1000000) (3223797 / 1000) (1582233 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3766983 / 1000000) (20224586237 / 250000) (1582233 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3766983 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3766983 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell869 :
    ∀ t ∈ Set.Icc ((9303 / 102400) : ℝ) (46547 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((599626713 / 500000000) : ℝ) ≤ Real.exp (2 * (9303 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9303 / 102400)) (599626713 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46547 / 512000) : ℝ)) ≤ (1199403343 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46547 / 512000)) (1199403343 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((81012735031 / 1000000) : ℝ) ≤ Real.exp (3 * (1883727 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1883727 / 500000)) (81012735031 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9303 / 102400) : ℝ) (46547 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1883727 / 500000) (1884023 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (9303 / 102400) (46547 / 512000) (599626713 / 500000000) (1199403343 / 1000000000) (1883727 / 500000) (1884023 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (9303 / 102400) (46547 / 512000) (1883727 / 500000) (1884023 / 500000) (17083 / 500) (8547 / 250)
    (58359 / 1000) (11741 / 200) (-562277 / 1000) (339469 / 1000000) (3225409 / 1000) (1579999 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1883727 / 500000) (81012735031 / 1000000) (1579999 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1883727 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1883727 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell870 :
    ∀ t ∈ Set.Icc ((46547 / 512000) : ℝ) (46579 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((599701671 / 500000000) : ℝ) ≤ Real.exp (2 * (46547 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46547 / 512000)) (599701671 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46579 / 512000) : ℝ)) ≤ (599776639 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46579 / 512000)) (599776639 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((81127286861 / 1000000) : ℝ) ≤ Real.exp (3 * (150717 / 40000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (150717 / 40000)) (81127286861 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46547 / 512000) : ℝ) (46579 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (150717 / 40000) (3768517 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46547 / 512000) (46579 / 512000) (599701671 / 500000000) (599776639 / 500000000) (150717 / 40000) (3768517 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46547 / 512000) (46579 / 512000) (150717 / 40000) (3768517 / 1000000) (34177 / 1000) (171 / 5)
    (2921 / 50) (29383 / 500) (-281171 / 500) (339117 / 1000000) (1613511 / 500) (197221 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (150717 / 40000) (81127286861 / 1000000) (197221 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (150717 / 40000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (150717 / 40000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell871 :
    ∀ t ∈ Set.Icc ((46579 / 512000) : ℝ) (46611 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1199553277 / 1000000000) : ℝ) ≤ Real.exp (2 * (46579 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46579 / 512000)) (1199553277 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46611 / 512000) : ℝ)) ≤ (18745363 / 15625000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46611 / 512000)) (18745363 / 15625000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((40621000333 / 500000) : ℝ) ≤ Real.exp (3 * (942099 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (942099 / 250000)) (40621000333 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46579 / 512000) : ℝ) (46611 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (942099 / 250000) (942247 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46579 / 512000) (46611 / 512000) (1199553277 / 1000000000) (18745363 / 15625000) (942099 / 250000) (942247 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46579 / 512000) (46611 / 512000) (942099 / 250000) (942247 / 250000) (34189 / 1000) (34211 / 1000)
    (58481 / 1000) (58827 / 1000) (-70301 / 125) (67753 / 200000) (807159 / 250) (78777 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (942099 / 250000) (40621000333 / 500000) (78777 / 25000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (942099 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (942099 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell872 :
    ∀ t ∈ Set.Icc ((46611 / 512000) : ℝ) (46643 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1199703231 / 1000000000) : ℝ) ≤ Real.exp (2 * (46611 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46611 / 512000)) (1199703231 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46643 / 512000) : ℝ)) ≤ (299963301 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46643 / 512000)) (299963301 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((81356876677 / 1000000) : ℝ) ≤ Real.exp (3 * (3768867 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3768867 / 1000000)) (81356876677 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46611 / 512000) : ℝ) (46643 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3768867 / 1000000) (3769459 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46611 / 512000) (46643 / 512000) (1199703231 / 1000000000) (299963301 / 250000000) (3768867 / 1000000) (3769459 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46611 / 512000) (46643 / 512000) (3768867 / 1000000) (3769459 / 1000000) (171 / 5) (34223 / 1000)
    (58543 / 1000) (7361 / 125) (-562473 / 1000) (338413 / 1000000) (12921 / 4) (3146631 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3768867 / 1000000) (81356876677 / 1000000) (3146631 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3768867 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3768867 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell873 :
    ∀ t ∈ Set.Icc ((46643 / 512000) : ℝ) (1867 / 20480), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1199853203 / 1000000000) : ℝ) ≤ Real.exp (2 * (46643 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46643 / 512000)) (1199853203 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1867 / 20480) : ℝ)) ≤ (240000639 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1867 / 20480)) (240000639 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((81471915121 / 1000000) : ℝ) ≤ Real.exp (3 * (1884669 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1884669 / 500000)) (81471915121 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46643 / 512000) : ℝ) (1867 / 20480),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1884669 / 500000) (3769931 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46643 / 512000) (1867 / 20480) (1199853203 / 1000000000) (240000639 / 200000000) (1884669 / 500000) (3769931 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46643 / 512000) (1867 / 20480) (1884669 / 500000) (3769931 / 1000000) (8553 / 250) (17117 / 500)
    (58603 / 1000) (1179 / 20) (-562533 / 1000) (169031 / 500000) (807967 / 250) (785547 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1884669 / 500000) (81471915121 / 1000000) (785547 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1884669 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1884669 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell874 :
    ∀ t ∈ Set.Icc ((1867 / 20480) : ℝ) (46707 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((600001597 / 500000000) : ℝ) ≤ Real.exp (2 * (1867 / 20480)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1867 / 20480)) (600001597 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46707 / 512000) : ℝ)) ≤ (240030641 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46707 / 512000)) (240030641 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2549605031 / 31250) : ℝ) ≤ Real.exp (3 * (376981 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (376981 / 100000)) (2549605031 / 31250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1867 / 20480) : ℝ) (46707 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (376981 / 100000) (1885201 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1867 / 20480) (46707 / 512000) (600001597 / 500000000) (240030641 / 200000000) (376981 / 100000) (1885201 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1867 / 20480) (46707 / 512000) (376981 / 100000) (1885201 / 500000) (34223 / 1000) (6849 / 200)
    (11733 / 200) (59011 / 1000) (-562603 / 1000) (33771 / 100000) (808371 / 250) (3137741 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (376981 / 100000) (2549605031 / 31250) (3137741 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (376981 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (376981 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell875 :
    ∀ t ∈ Set.Icc ((46707 / 512000) : ℝ) (46739 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((300038301 / 250000000) : ℝ) ≤ Real.exp (2 * (46707 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46707 / 512000)) (300038301 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46739 / 512000) : ℝ)) ≤ (1200303233 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46739 / 512000)) (1200303233 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4085136267 / 50000) : ℝ) ≤ Real.exp (3 * (3770281 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3770281 / 1000000)) (4085136267 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46707 / 512000) : ℝ) (46739 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3770281 / 1000000) (3770873 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46707 / 512000) (46739 / 512000) (300038301 / 250000000) (1200303233 / 1000000000) (3770281 / 1000000) (3770873 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46707 / 512000) (46739 / 512000) (3770281 / 1000000) (3770873 / 1000000) (17117 / 500) (34257 / 1000)
    (29363 / 500) (7384 / 125) (-140667 / 250) (4217 / 12500) (32351 / 10) (3133311 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3770281 / 1000000) (4085136267 / 50000) (3133311 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3770281 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3770281 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell876 :
    ∀ t ∈ Set.Icc ((46739 / 512000) : ℝ) (46771 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((9377369 / 7812500) : ℝ) ≤ Real.exp (2 * (46739 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46739 / 512000)) (9377369 / 7812500) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46771 / 512000) : ℝ)) ≤ (7502833 / 6250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46771 / 512000)) (7502833 / 6250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((40909126407 / 500000) : ℝ) ≤ Real.exp (3 * (58918 / 15625)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (58918 / 15625)) (40909126407 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46739 / 512000) : ℝ) (46771 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (58918 / 15625) (754269 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46739 / 512000) (46771 / 512000) (9377369 / 7812500) (7502833 / 6250000) (58918 / 15625) (754269 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46739 / 512000) (46771 / 512000) (58918 / 15625) (754269 / 200000) (17123 / 500) (8567 / 250)
    (58787 / 1000) (29567 / 500) (-70341 / 125) (33701 / 100000) (80918 / 25) (3128887 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (58918 / 15625) (40909126407 / 500000) (3128887 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (58918 / 15625)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (58918 / 15625)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell877 :
    ∀ t ∈ Set.Icc ((46771 / 512000) : ℝ) (46803 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1200453279 / 1000000000) : ℝ) ≤ Real.exp (2 * (46771 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46771 / 512000)) (1200453279 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46803 / 512000) : ℝ)) ≤ (600301673 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46803 / 512000)) (600301673 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((81933943643 / 1000000) : ℝ) ≤ Real.exp (3 * (3771223 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3771223 / 1000000)) (81933943643 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46771 / 512000) : ℝ) (46803 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3771223 / 1000000) (471477 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46771 / 512000) (46803 / 512000) (1200453279 / 1000000000) (600301673 / 500000000) (3771223 / 1000000) (471477 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46771 / 512000) (46803 / 512000) (3771223 / 1000000) (471477 / 125000) (34257 / 1000) (857 / 25)
    (7356 / 125) (11839 / 200) (-562793 / 1000) (16833 / 50000) (3238337 / 1000) (3124469 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3771223 / 1000000) (81933943643 / 1000000) (3124469 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3771223 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3771223 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell878 :
    ∀ t ∈ Set.Icc ((46803 / 512000) : ℝ) (9367 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((240120669 / 200000000) : ℝ) ≤ Real.exp (2 * (46803 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (46803 / 512000)) (240120669 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9367 / 102400) : ℝ)) ≤ (1200753431 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9367 / 102400)) (1200753431 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((5128127763 / 62500) : ℝ) ≤ Real.exp (3 * (754339 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (754339 / 200000)) (5128127763 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((46803 / 512000) : ℝ) (9367 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (754339 / 200000) (3772287 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (46803 / 512000) (9367 / 102400) (240120669 / 200000000) (1200753431 / 1000000000) (754339 / 200000) (3772287 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (46803 / 512000) (9367 / 102400) (754339 / 200000) (3772287 / 1000000) (34269 / 1000) (34291 / 1000)
    (5891 / 100) (7407 / 125) (-281431 / 500) (33631 / 100000) (647991 / 200) (195003 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (754339 / 200000) (5128127763 / 62500) (195003 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (754339 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (754339 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell879 :
    ∀ t ∈ Set.Icc ((9367 / 102400) : ℝ) (46867 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((120075343 / 100000000) : ℝ) ≤ Real.exp (2 * (9367 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9367 / 102400)) (120075343 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((46867 / 512000) : ℝ)) ≤ (240180707 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (46867 / 512000)) (240180707 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((82166062789 / 1000000) : ℝ) ≤ Real.exp (3 * (1886083 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1886083 / 500000)) (82166062789 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9367 / 102400) : ℝ) (46867 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1886083 / 500000) (3772759 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (9367 / 102400) (46867 / 512000) (120075343 / 100000000) (240180707 / 200000000) (1886083 / 500000) (3772759 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (9367 / 102400) (46867 / 512000) (1886083 / 500000) (3772759 / 1000000) (857 / 25) (17151 / 500)
    (58971 / 1000) (29659 / 500) (-281461 / 500) (335961 / 1000000) (3241577 / 1000) (1557821 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1886083 / 500000) (82166062789 / 1000000) (1557821 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1886083 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1886083 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch043 :
    ∀ t ∈ Set.Icc ((46307 / 512000) : ℝ) (46867 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell860
      hpThetaDensityLowerExpCompact_cell861)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell862
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell863
      hpThetaDensityLowerExpCompact_cell864)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell865
      hpThetaDensityLowerExpCompact_cell866)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell867
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell868
      hpThetaDensityLowerExpCompact_cell869))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell870
      hpThetaDensityLowerExpCompact_cell871)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell872
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell873
      hpThetaDensityLowerExpCompact_cell874)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell875
      hpThetaDensityLowerExpCompact_cell876)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell877
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell878
      hpThetaDensityLowerExpCompact_cell879)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch043
end HodgeProofHP
