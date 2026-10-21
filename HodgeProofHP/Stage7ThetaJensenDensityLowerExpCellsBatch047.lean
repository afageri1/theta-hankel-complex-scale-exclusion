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
theorem hpThetaDensityLowerExpCompact_cell940 :
    ∀ t ∈ Set.Icc ((48787 / 512000) : ℝ) (48819 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((120994417 / 100000000) : ℝ) ≤ Real.exp (2 * (48787 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (48787 / 512000)) (120994417 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((48819 / 512000) : ℝ)) ≤ (18907741 / 15625000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (48819 / 512000)) (18907741 / 15625000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((280001672 / 3125) : ℝ) ≤ Real.exp (3 * (3801039 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3801039 / 1000000)) (280001672 / 3125) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((48787 / 512000) : ℝ) (48819 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3801039 / 1000000) (950409 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (48787 / 512000) (48819 / 512000) (120994417 / 100000000) (18907741 / 15625000) (3801039 / 1000000) (950409 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (48787 / 512000) (48819 / 512000) (3801039 / 1000000) (950409 / 250000) (34981 / 1000) (8751 / 250)
    (31389 / 500) (63131 / 1000) (-283313 / 500) (157607 / 500000) (3341967 / 1000) (1428563 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3801039 / 1000000) (280001672 / 3125) (1428563 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3801039 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3801039 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell941 :
    ∀ t ∈ Set.Icc ((48819 / 512000) : ℝ) (48851 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1210095423 / 1000000000) : ℝ) ≤ Real.exp (2 * (48819 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (48819 / 512000)) (1210095423 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((48851 / 512000) : ℝ)) ≤ (242049339 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (48851 / 512000)) (242049339 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((22432076679 / 250000) : ℝ) ≤ Real.exp (3 * (1900757 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1900757 / 500000)) (22432076679 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((48819 / 512000) : ℝ) (48851 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1900757 / 500000) (59408 / 15625) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (48819 / 512000) (48851 / 512000) (1210095423 / 1000000000) (242049339 / 200000000) (1900757 / 500000) (59408 / 15625) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (48819 / 512000) (48851 / 512000) (1900757 / 500000) (59408 / 15625) (34993 / 1000) (4377 / 125)
    (62841 / 1000) (12639 / 200) (-566679 / 1000) (314883 / 1000000) (3343641 / 1000) (1426529 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1900757 / 500000) (22432076679 / 250000) (1426529 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1900757 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1900757 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell942 :
    ∀ t ∈ Set.Icc ((48851 / 512000) : ℝ) (48883 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((605123347 / 500000000) : ℝ) ≤ Real.exp (2 * (48851 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (48851 / 512000)) (605123347 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((48883 / 512000) : ℝ)) ≤ (242079597 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (48883 / 512000)) (242079597 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((89856260597 / 1000000) : ℝ) ≤ Real.exp (3 * (3801989 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3801989 / 1000000)) (89856260597 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((48851 / 512000) : ℝ) (48883 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3801989 / 1000000) (3802587 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (48851 / 512000) (48883 / 512000) (605123347 / 500000000) (242079597 / 200000000) (3801989 / 1000000) (3802587 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (48851 / 512000) (48883 / 512000) (3801989 / 1000000) (3802587 / 1000000) (8751 / 250) (35027 / 1000)
    (12581 / 200) (63259 / 1000) (-70842 / 125) (314553 / 1000000) (418164 / 125) (569799 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3801989 / 1000000) (89856260597 / 1000000) (569799 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3801989 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3801989 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell943 :
    ∀ t ∈ Set.Icc ((48883 / 512000) : ℝ) (9783 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((37824937 / 31250000) : ℝ) ≤ Real.exp (2 * (48883 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (48883 / 512000)) (37824937 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9783 / 102400) : ℝ)) ≤ (242109859 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9783 / 102400)) (242109859 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((44992333447 / 500000) : ℝ) ≤ Real.exp (3 * (760493 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (760493 / 200000)) (44992333447 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((48883 / 512000) : ℝ) (9783 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (760493 / 200000) (1901531 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (48883 / 512000) (9783 / 102400) (37824937 / 31250000) (242109859 / 200000000) (760493 / 200000) (1901531 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (48883 / 512000) (9783 / 102400) (760493 / 200000) (1901531 / 500000) (4377 / 125) (35039 / 1000)
    (62969 / 1000) (31661 / 500) (-283399 / 500) (157111 / 500000) (418373 / 125) (284493 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (760493 / 200000) (44992333447 / 500000) (284493 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (760493 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (760493 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell944 :
    ∀ t ∈ Set.Icc ((9783 / 102400) : ℝ) (48947 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((605274647 / 500000000) : ℝ) ≤ Real.exp (2 * (9783 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9783 / 102400)) (605274647 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((48947 / 512000) : ℝ)) ≤ (1210700623 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (48947 / 512000)) (1210700623 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((22528246587 / 250000) : ℝ) ≤ Real.exp (3 * (190147 / 50000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (190147 / 50000)) (22528246587 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9783 / 102400) : ℝ) (48947 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (190147 / 50000) (1901769 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (9783 / 102400) (48947 / 512000) (605274647 / 500000000) (1210700623 / 1000000000) (190147 / 50000) (1901769 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (9783 / 102400) (48947 / 512000) (190147 / 50000) (1901769 / 500000) (8757 / 250) (701 / 20)
    (7879 / 125) (31693 / 500) (-566851 / 1000) (78473 / 250000) (167433 / 50) (1420439 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (190147 / 50000) (22528246587 / 250000) (1420439 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (190147 / 50000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (190147 / 50000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell945 :
    ∀ t ∈ Set.Icc ((48947 / 512000) : ℝ) (48979 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((605350311 / 500000000) : ℝ) ≤ Real.exp (2 * (48947 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (48947 / 512000)) (605350311 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((48979 / 512000) : ℝ)) ≤ (121085197 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (48979 / 512000)) (121085197 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((90241759511 / 1000000) : ℝ) ≤ Real.exp (3 * (475427 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (475427 / 125000)) (90241759511 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((48947 / 512000) : ℝ) (48979 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (475427 / 125000) (3804013 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (48947 / 512000) (48979 / 512000) (605350311 / 500000000) (121085197 / 100000000) (475427 / 125000) (3804013 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (48947 / 512000) (48979 / 512000) (475427 / 125000) (3804013 / 1000000) (35039 / 1000) (17531 / 500)
    (7887 / 125) (1269 / 20) (-566913 / 1000) (156781 / 500000) (3350333 / 1000) (113473 / 40000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (475427 / 125000) (90241759511 / 1000000) (113473 / 40000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (475427 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (475427 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell946 :
    ∀ t ∈ Set.Icc ((48979 / 512000) : ℝ) (49011 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1210851969 / 1000000000) : ℝ) ≤ Real.exp (2 * (48979 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (48979 / 512000)) (1210851969 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((49011 / 512000) : ℝ)) ≤ (151375417 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (49011 / 512000)) (151375417 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((45185222791 / 500000) : ℝ) ≤ Real.exp (3 * (3803891 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3803891 / 1000000)) (45185222791 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((48979 / 512000) : ℝ) (49011 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3803891 / 1000000) (3804489 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (48979 / 512000) (49011 / 512000) (1210851969 / 1000000000) (151375417 / 125000000) (3803891 / 1000000) (3804489 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (48979 / 512000) (49011 / 512000) (3803891 / 1000000) (3804489 / 1000000) (35051 / 1000) (17537 / 500)
    (1579 / 25) (31757 / 500) (-113393 / 200) (313233 / 1000000) (3352011 / 1000) (566557 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3803891 / 1000000) (45185222791 / 500000) (566557 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3803891 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3803891 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell947 :
    ∀ t ∈ Set.Icc ((49011 / 512000) : ℝ) (49043 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((242200667 / 200000000) : ℝ) ≤ Real.exp (2 * (49011 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (49011 / 512000)) (242200667 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((49043 / 512000) : ℝ)) ≤ (1211154721 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (49043 / 512000)) (1211154721 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2262482879 / 25000) : ℝ) ≤ Real.exp (3 * (1902183 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1902183 / 500000)) (2262482879 / 25000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((49011 / 512000) : ℝ) (49043 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1902183 / 500000) (951241 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (49011 / 512000) (49043 / 512000) (242200667 / 200000000) (1211154721 / 1000000000) (1902183 / 500000) (951241 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (49011 / 512000) (49043 / 512000) (1902183 / 500000) (951241 / 250000) (35063 / 1000) (7017 / 200)
    (63223 / 1000) (31789 / 500) (-567021 / 1000) (39113 / 125000) (670737 / 200) (2828751 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1902183 / 500000) (2262482879 / 25000) (2828751 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1902183 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1902183 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell948 :
    ∀ t ∈ Set.Icc ((49043 / 512000) : ℝ) (1963 / 20480), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((7569717 / 6250000) : ℝ) ≤ Real.exp (2 * (49043 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (49043 / 512000)) (7569717 / 6250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1963 / 20480) : ℝ)) ≤ (302826531 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1963 / 20480)) (302826531 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((45314320197 / 500000) : ℝ) ≤ Real.exp (3 * (1902421 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1902421 / 500000)) (45314320197 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((49043 / 512000) : ℝ) (1963 / 20480),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1902421 / 500000) (11892 / 3125) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (49043 / 512000) (1963 / 20480) (7569717 / 6250000) (302826531 / 250000000) (1902421 / 500000) (11892 / 3125) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (49043 / 512000) (1963 / 20480) (1902421 / 500000) (11892 / 3125) (17537 / 500) (35097 / 1000)
    (63287 / 1000) (63641 / 1000) (-283539 / 500) (12503 / 40000) (3355363 / 1000) (564943 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1902421 / 500000) (45314320197 / 500000) (564943 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1902421 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1902421 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell949 :
    ∀ t ∈ Set.Icc ((1963 / 20480) : ℝ) (49107 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1211306123 / 1000000000) : ℝ) ≤ Real.exp (2 * (1963 / 20480)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1963 / 20480)) (1211306123 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((49107 / 512000) : ℝ)) ≤ (1211457547 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (49107 / 512000)) (1211457547 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((18151630087 / 200000) : ℝ) ≤ Real.exp (3 * (1902659 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1902659 / 500000)) (18151630087 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1963 / 20480) : ℝ) (49107 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1902659 / 500000) (951479 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1963 / 20480) (49107 / 512000) (1211306123 / 1000000000) (1211457547 / 1000000000) (1902659 / 500000) (951479 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1963 / 20480) (49107 / 512000) (1902659 / 500000) (951479 / 250000) (17543 / 500) (35109 / 1000)
    (63351 / 1000) (12741 / 200) (-113427 / 200) (156123 / 500000) (3357043 / 1000) (705171 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1902659 / 500000) (18151630087 / 200000) (705171 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1902659 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1902659 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell950 :
    ∀ t ∈ Set.Icc ((49107 / 512000) : ℝ) (49139 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((605728773 / 500000000) : ℝ) ≤ Real.exp (2 * (49107 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (49107 / 512000)) (605728773 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((49139 / 512000) : ℝ)) ≤ (1211608989 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (49139 / 512000)) (1211608989 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((45443786443 / 500000) : ℝ) ≤ Real.exp (3 * (3805793 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3805793 / 1000000)) (45443786443 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((49107 / 512000) : ℝ) (49139 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3805793 / 1000000) (3806391 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (49107 / 512000) (49139 / 512000) (605728773 / 500000000) (1211608989 / 1000000000) (3805793 / 1000000) (3806391 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (49107 / 512000) (49139 / 512000) (3805793 / 1000000) (3806391 / 1000000) (35097 / 1000) (878 / 25)
    (12683 / 200) (63769 / 1000) (-567191 / 1000) (155959 / 500000) (3358719 / 1000) (2816667 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3805793 / 1000000) (45443786443 / 500000) (2816667 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3805793 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3805793 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell951 :
    ∀ t ∈ Set.Icc ((49139 / 512000) : ℝ) (49171 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((302902247 / 250000000) : ℝ) ≤ Real.exp (2 * (49139 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (49139 / 512000)) (302902247 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((49171 / 512000) : ℝ)) ≤ (1211760449 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (49171 / 512000)) (1211760449 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((45508726473 / 500000) : ℝ) ≤ Real.exp (3 * (3806269 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3806269 / 1000000)) (45508726473 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((49139 / 512000) : ℝ) (49171 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3806269 / 1000000) (3806867 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (49139 / 512000) (49171 / 512000) (302902247 / 250000000) (1211760449 / 1000000000) (3806269 / 1000000) (3806867 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (49139 / 512000) (49171 / 512000) (3806269 / 1000000) (3806867 / 1000000) (35109 / 1000) (8783 / 250)
    (63479 / 1000) (63833 / 1000) (-567247 / 1000) (31159 / 100000) (3360399 / 1000) (351581 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3806269 / 1000000) (45508726473 / 500000) (351581 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3806269 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3806269 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell952 :
    ∀ t ∈ Set.Icc ((49171 / 512000) : ℝ) (49203 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((18933757 / 15625000) : ℝ) ≤ Real.exp (2 * (49171 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (49171 / 512000)) (18933757 / 15625000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((49203 / 512000) : ℝ)) ≤ (1211911929 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (49203 / 512000)) (1211911929 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((5696719913 / 62500) : ℝ) ≤ Real.exp (3 * (761349 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (761349 / 200000)) (5696719913 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((49171 / 512000) : ℝ) (49203 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (761349 / 200000) (3807343 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (49171 / 512000) (49203 / 512000) (18933757 / 15625000) (1211911929 / 1000000000) (761349 / 200000) (3807343 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (49171 / 512000) (49203 / 512000) (761349 / 200000) (3807343 / 1000000) (35121 / 1000) (35143 / 1000)
    (63543 / 1000) (63897 / 1000) (-70913 / 125) (155631 / 500000) (84052 / 25) (1404317 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (761349 / 200000) (5696719913 / 62500) (1404317 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (761349 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (761349 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell953 :
    ∀ t ∈ Set.Icc ((49203 / 512000) : ℝ) (9847 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((151488991 / 125000000) : ℝ) ≤ Real.exp (2 * (49203 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (49203 / 512000)) (151488991 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9847 / 102400) : ℝ)) ≤ (1212063427 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9847 / 102400)) (1212063427 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((18255554027 / 200000) : ℝ) ≤ Real.exp (3 * (3807221 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3807221 / 1000000)) (18255554027 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((49203 / 512000) : ℝ) (9847 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3807221 / 1000000) (3807819 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (49203 / 512000) (9847 / 102400) (151488991 / 125000000) (1212063427 / 1000000000) (3807221 / 1000000) (3807819 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (49203 / 512000) (9847 / 102400) (3807221 / 1000000) (3807819 / 1000000) (8783 / 250) (7031 / 200)
    (63607 / 1000) (63961 / 1000) (-14184 / 25) (155467 / 500000) (1681881 / 500) (1402313 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3807221 / 1000000) (18255554027 / 200000) (1402313 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3807221 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3807221 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell954 :
    ∀ t ∈ Set.Icc ((9847 / 102400) : ℝ) (49267 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((606031713 / 500000000) : ℝ) ≤ Real.exp (2 * (9847 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9847 / 102400)) (606031713 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((49267 / 512000) : ℝ)) ≤ (242442989 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (49267 / 512000)) (242442989 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((45704103897 / 500000) : ℝ) ≤ Real.exp (3 * (3807697 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3807697 / 1000000)) (45704103897 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9847 / 102400) : ℝ) (49267 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3807697 / 1000000) (761659 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (9847 / 102400) (49267 / 512000) (606031713 / 500000000) (242442989 / 200000000) (3807697 / 1000000) (761659 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (9847 / 102400) (49267 / 512000) (3807697 / 1000000) (761659 / 200000) (4393 / 125) (35167 / 1000)
    (63671 / 1000) (2561 / 40) (-70927 / 125) (310607 / 1000000) (841361 / 250) (175039 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3807697 / 1000000) (45704103897 / 500000) (175039 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3807697 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3807697 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell955 :
    ∀ t ∈ Set.Icc ((49267 / 512000) : ℝ) (49299 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((37881717 / 31250000) : ℝ) ≤ Real.exp (2 * (49267 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (49267 / 512000)) (37881717 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((49299 / 512000) : ℝ)) ≤ (1212366481 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (49299 / 512000)) (1212366481 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1830776637 / 20000) : ℝ) ≤ Real.exp (3 * (3808173 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3808173 / 1000000)) (1830776637 / 20000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((49267 / 512000) : ℝ) (49299 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3808173 / 1000000) (3808771 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (49267 / 512000) (49299 / 512000) (37881717 / 31250000) (1212366481 / 1000000000) (3808173 / 1000000) (3808771 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (49267 / 512000) (49299 / 512000) (3808173 / 1000000) (3808771 / 1000000) (8789 / 250) (17589 / 500)
    (12747 / 200) (64089 / 1000) (-567471 / 1000) (7757 / 25000) (3367127 / 1000) (699157 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3808173 / 1000000) (1830776637 / 20000) (699157 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3808173 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3808173 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell956 :
    ∀ t ∈ Set.Icc ((49299 / 512000) : ℝ) (49331 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((15154581 / 12500000) : ℝ) ≤ Real.exp (2 * (49299 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (49299 / 512000)) (15154581 / 12500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((49331 / 512000) : ℝ)) ≤ (303129509 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (49331 / 512000)) (303129509 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((91669642571 / 1000000) : ℝ) ≤ Real.exp (3 * (3808649 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3808649 / 1000000)) (91669642571 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((49299 / 512000) : ℝ) (49331 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3808649 / 1000000) (3809247 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (49299 / 512000) (49331 / 512000) (15154581 / 12500000) (303129509 / 250000000) (3808649 / 1000000) (3809247 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (49299 / 512000) (49331 / 512000) (3808649 / 1000000) (3809247 / 1000000) (35167 / 1000) (3519 / 100)
    (63799 / 1000) (64153 / 1000) (-567527 / 1000) (309953 / 1000000) (3368811 / 1000) (2792637 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3808649 / 1000000) (91669642571 / 1000000) (2792637 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3808649 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3808649 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell957 :
    ∀ t ∈ Set.Icc ((49331 / 512000) : ℝ) (49363 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((242503607 / 200000000) : ℝ) ≤ Real.exp (2 * (49331 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (49331 / 512000)) (242503607 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((49363 / 512000) : ℝ)) ≤ (1212669611 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (49363 / 512000)) (1212669611 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((45900320111 / 500000) : ℝ) ≤ Real.exp (3 * (30473 / 8000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (30473 / 8000)) (45900320111 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((49331 / 512000) : ℝ) (49363 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (30473 / 8000) (3809723 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (49331 / 512000) (49363 / 512000) (242503607 / 200000000) (1212669611 / 1000000000) (30473 / 8000) (3809723 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (49331 / 512000) (49363 / 512000) (30473 / 8000) (3809723 / 1000000) (35179 / 1000) (17601 / 500)
    (63863 / 1000) (32109 / 500) (-567583 / 1000) (309627 / 1000000) (674099 / 200) (697163 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (30473 / 8000) (45900320111 / 500000) (697163 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (30473 / 8000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (30473 / 8000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell958 :
    ∀ t ∈ Set.Icc ((49363 / 512000) : ℝ) (9879 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((121266961 / 100000000) : ℝ) ≤ Real.exp (2 * (49363 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (49363 / 512000)) (121266961 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9879 / 102400) : ℝ)) ≤ (303205301 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9879 / 102400)) (303205301 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((91931825071 / 1000000) : ℝ) ≤ Real.exp (3 * (3809601 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3809601 / 1000000)) (91931825071 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((49363 / 512000) : ℝ) (9879 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3809601 / 1000000) (19051 / 5000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (49363 / 512000) (9879 / 102400) (121266961 / 100000000) (303205301 / 250000000) (3809601 / 1000000) (19051 / 5000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (49363 / 512000) (9879 / 102400) (3809601 / 1000000) (19051 / 5000) (35191 / 1000) (35213 / 1000)
    (63927 / 1000) (32141 / 500) (-567633 / 1000) (309301 / 1000000) (3372183 / 1000) (2784673 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3809601 / 1000000) (91931825071 / 1000000) (2784673 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3809601 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3809601 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell959 :
    ∀ t ∈ Set.Icc ((9879 / 102400) : ℝ) (49427 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1212821203 / 1000000000) : ℝ) ≤ Real.exp (2 * (9879 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9879 / 102400)) (1212821203 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((49427 / 512000) : ℝ)) ≤ (75810801 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (49427 / 512000)) (75810801 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((18412639477 / 200000) : ℝ) ≤ Real.exp (3 * (3810077 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3810077 / 1000000)) (18412639477 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9879 / 102400) : ℝ) (49427 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3810077 / 1000000) (952669 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (9879 / 102400) (49427 / 512000) (1212821203 / 1000000000) (75810801 / 62500000) (3810077 / 1000000) (952669 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (9879 / 102400) (49427 / 512000) (3810077 / 1000000) (952669 / 250000) (17601 / 500) (1409 / 40)
    (63991 / 1000) (32173 / 500) (-567689 / 1000) (19311 / 62500) (843467 / 250) (2780699 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3810077 / 1000000) (18412639477 / 200000) (2780699 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3810077 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3810077 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch047 :
    ∀ t ∈ Set.Icc ((48787 / 512000) : ℝ) (49427 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell940
      hpThetaDensityLowerExpCompact_cell941)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell942
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell943
      hpThetaDensityLowerExpCompact_cell944)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell945
      hpThetaDensityLowerExpCompact_cell946)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell947
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell948
      hpThetaDensityLowerExpCompact_cell949))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell950
      hpThetaDensityLowerExpCompact_cell951)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell952
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell953
      hpThetaDensityLowerExpCompact_cell954)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell955
      hpThetaDensityLowerExpCompact_cell956)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell957
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell958
      hpThetaDensityLowerExpCompact_cell959)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch047
end HodgeProofHP
