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
theorem hpThetaDensityLowerExpCompact_cell720 :
    ∀ t ∈ Set.Icc ((44067 / 512000) : ℝ) (44083 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((593920111 / 500000000) : ℝ) ≤ Real.exp (2 * (44067 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44067 / 512000)) (593920111 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44083 / 512000) : ℝ)) ≤ (237582893 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44083 / 512000)) (237582893 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((18187782351 / 250000) : ℝ) ≤ Real.exp (3 * (9329 / 2500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (9329 / 2500)) (18187782351 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44067 / 512000) : ℝ) (44083 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (9329 / 2500) (3731953 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44067 / 512000) (44083 / 512000) (593920111 / 500000000) (237582893 / 200000000) (9329 / 2500) (3731953 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44067 / 512000) (44083 / 512000) (9329 / 2500) (3731953 / 1000000) (33307 / 1000) (33321 / 1000)
    (10769 / 200) (6756 / 125) (-111609 / 200) (18363 / 50000) (3103593 / 1000) (1759423 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (9329 / 2500) (18187782351 / 250000) (1759423 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (9329 / 2500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (9329 / 2500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell721 :
    ∀ t ∈ Set.Icc ((44083 / 512000) : ℝ) (44099 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((37122327 / 31250000) : ℝ) ≤ Real.exp (2 * (44083 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44083 / 512000)) (37122327 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44099 / 512000) : ℝ)) ≤ (148498589 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44099 / 512000)) (148498589 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((72802000193 / 1000000) : ℝ) ≤ Real.exp (3 * (3731833 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3731833 / 1000000)) (72802000193 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44083 / 512000) : ℝ) (44099 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3731833 / 1000000) (1866093 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44083 / 512000) (44099 / 512000) (37122327 / 31250000) (148498589 / 125000000) (3731833 / 1000000) (1866093 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44083 / 512000) (44099 / 512000) (3731833 / 1000000) (1866093 / 500000) (33313 / 1000) (16663 / 500)
    (26937 / 500) (54077 / 1000) (-279041 / 500) (11471 / 31250) (388046 / 125) (3516387 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3731833 / 1000000) (72802000193 / 1000000) (3516387 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3731833 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3731833 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell722 :
    ∀ t ∈ Set.Icc ((44099 / 512000) : ℝ) (8823 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1187988711 / 1000000000) : ℝ) ≤ Real.exp (2 * (44099 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44099 / 512000)) (1187988711 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8823 / 102400) : ℝ)) ≤ (297015741 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8823 / 102400)) (297015741 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((9106613319 / 125000) : ℝ) ≤ Real.exp (3 * (1866033 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1866033 / 500000)) (9106613319 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44099 / 512000) : ℝ) (8823 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1866033 / 500000) (3732419 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44099 / 512000) (8823 / 102400) (1187988711 / 1000000000) (297015741 / 250000000) (1866033 / 500000) (3732419 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44099 / 512000) (8823 / 102400) (1866033 / 500000) (3732419 / 1000000) (16659 / 500) (8333 / 250)
    (53903 / 1000) (27053 / 500) (-558119 / 1000) (91721 / 250000) (3105143 / 1000) (351393 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1866033 / 500000) (9106613319 / 125000) (351393 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1866033 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1866033 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell723 :
    ∀ t ∈ Set.Icc ((8823 / 102400) : ℝ) (44131 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1188062963 / 1000000000) : ℝ) ≤ Real.exp (2 * (8823 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8823 / 102400)) (1188062963 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44131 / 512000) : ℝ)) ≤ (59406861 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44131 / 512000)) (59406861 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((18225962127 / 250000) : ℝ) ≤ Real.exp (3 * (3732299 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3732299 / 1000000)) (18225962127 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8823 / 102400) : ℝ) (44131 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3732299 / 1000000) (933163 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8823 / 102400) (44131 / 512000) (1188062963 / 1000000000) (59406861 / 50000000) (3732299 / 1000000) (933163 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8823 / 102400) (44131 / 512000) (3732299 / 1000000) (933163 / 250000) (8331 / 250) (33337 / 1000)
    (13483 / 250) (6767 / 125) (-139539 / 250) (45837 / 125000) (3105919 / 1000) (140459 / 40000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3732299 / 1000000) (18225962127 / 250000) (140459 / 40000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3732299 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3732299 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell724 :
    ∀ t ∈ Set.Icc ((44131 / 512000) : ℝ) (44147 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1188137219 / 1000000000) : ℝ) ≤ Real.exp (2 * (44131 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44131 / 512000)) (1188137219 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44147 / 512000) : ℝ)) ≤ (1188211481 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44147 / 512000)) (1188211481 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((72955044949 / 1000000) : ℝ) ≤ Real.exp (3 * (3732533 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3732533 / 1000000)) (72955044949 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44131 / 512000) : ℝ) (44147 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3732533 / 1000000) (1866443 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44131 / 512000) (44147 / 512000) (1188137219 / 1000000000) (1188211481 / 1000000000) (3732533 / 1000000) (1866443 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44131 / 512000) (44147 / 512000) (3732533 / 1000000) (1866443 / 500000) (33329 / 1000) (33343 / 1000)
    (26981 / 500) (10833 / 200) (-558193 / 1000) (91627 / 250000) (3106697 / 1000) (3509011 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3732533 / 1000000) (72955044949 / 1000000) (3509011 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3732533 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3732533 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell725 :
    ∀ t ∈ Set.Icc ((44147 / 512000) : ℝ) (44163 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((29705287 / 25000000) : ℝ) ≤ Real.exp (2 * (44147 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44147 / 512000)) (29705287 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44163 / 512000) : ℝ)) ≤ (594142873 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44163 / 512000)) (594142873 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((18251514581 / 250000) : ℝ) ≤ Real.exp (3 * (1866383 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1866383 / 500000)) (18251514581 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44147 / 512000) : ℝ) (44163 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1866383 / 500000) (3733119 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44147 / 512000) (44163 / 512000) (29705287 / 25000000) (594142873 / 500000000) (1866383 / 500000) (3733119 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44147 / 512000) (44163 / 512000) (1866383 / 500000) (3733119 / 1000000) (6667 / 200) (33349 / 1000)
    (53991 / 1000) (27097 / 500) (-558229 / 1000) (4579 / 12500) (3107473 / 1000) (3506559 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1866383 / 500000) (18251514581 / 250000) (3506559 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1866383 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1866383 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell726 :
    ∀ t ∈ Set.Icc ((44163 / 512000) : ℝ) (44179 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((237657149 / 200000000) : ℝ) ≤ Real.exp (2 * (44163 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44163 / 512000)) (237657149 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44179 / 512000) : ℝ)) ≤ (74272501 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44179 / 512000)) (74272501 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((7305710737 / 100000) : ℝ) ≤ Real.exp (3 * (3732999 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3732999 / 1000000)) (7305710737 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44163 / 512000) : ℝ) (44179 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3732999 / 1000000) (466669 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44163 / 512000) (44179 / 512000) (237657149 / 200000000) (74272501 / 62500000) (3732999 / 1000000) (466669 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44163 / 512000) (44179 / 512000) (3732999 / 1000000) (466669 / 125000) (33341 / 1000) (16677 / 500)
    (2701 / 50) (6778 / 125) (-279133 / 500) (366133 / 1000000) (3108249 / 1000) (3504109 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3732999 / 1000000) (7305710737 / 100000) (3504109 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3732999 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3732999 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell727 :
    ∀ t ∈ Set.Icc ((44179 / 512000) : ℝ) (8839 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((237672003 / 200000000) : ℝ) ≤ Real.exp (2 * (44179 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44179 / 512000)) (237672003 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8839 / 102400) : ℝ)) ≤ (1188434291 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8839 / 102400)) (1188434291 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4569262007 / 62500) : ℝ) ≤ Real.exp (3 * (233327 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (233327 / 62500)) (4569262007 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44179 / 512000) : ℝ) (8839 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (233327 / 62500) (1866793 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44179 / 512000) (8839 / 102400) (237672003 / 200000000) (1188434291 / 1000000000) (233327 / 62500) (1866793 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44179 / 512000) (8839 / 102400) (233327 / 62500) (1866793 / 500000) (16673 / 500) (834 / 25)
    (54049 / 1000) (54253 / 1000) (-279149 / 500) (182973 / 500000) (777257 / 250) (175083 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (233327 / 62500) (4569262007 / 62500) (175083 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (233327 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (233327 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell728 :
    ∀ t ∈ Set.Icc ((8839 / 102400) : ℝ) (44211 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((118843429 / 100000000) : ℝ) ≤ Real.exp (2 * (8839 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8839 / 102400)) (118843429 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44211 / 512000) : ℝ)) ≤ (1188508571 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44211 / 512000)) (1188508571 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((18289883013 / 250000) : ℝ) ≤ Real.exp (3 * (1866733 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1866733 / 500000)) (18289883013 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8839 / 102400) : ℝ) (44211 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1866733 / 500000) (3733819 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8839 / 102400) (44211 / 512000) (118843429 / 100000000) (1188508571 / 1000000000) (1866733 / 500000) (3733819 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8839 / 102400) (44211 / 512000) (1866733 / 500000) (3733819 / 1000000) (4169 / 125) (6673 / 200)
    (54079 / 1000) (27141 / 500) (-558339 / 1000) (365757 / 1000000) (621961 / 200) (3499203 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1866733 / 500000) (18289883013 / 250000) (3499203 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1866733 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1866733 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell729 :
    ∀ t ∈ Set.Icc ((44211 / 512000) : ℝ) (44227 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((118850857 / 100000000) : ℝ) ≤ Real.exp (2 * (44211 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44211 / 512000)) (118850857 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44227 / 512000) : ℝ)) ≤ (237716571 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44227 / 512000)) (237716571 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((36605344207 / 500000) : ℝ) ≤ Real.exp (3 * (3733699 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3733699 / 1000000)) (36605344207 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44211 / 512000) : ℝ) (44227 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3733699 / 1000000) (933513 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44211 / 512000) (44227 / 512000) (118850857 / 100000000) (237716571 / 200000000) (3733699 / 1000000) (933513 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44211 / 512000) (44227 / 512000) (3733699 / 1000000) (933513 / 250000) (33357 / 1000) (33371 / 1000)
    (13527 / 250) (54311 / 1000) (-69797 / 125) (36557 / 100000) (3110581 / 1000) (1748379 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3733699 / 1000000) (36605344207 / 500000) (1748379 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3733699 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3733699 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell730 :
    ∀ t ∈ Set.Icc ((44227 / 512000) : ℝ) (44243 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((594291427 / 500000000) : ℝ) ≤ Real.exp (2 * (44227 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44227 / 512000)) (594291427 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44243 / 512000) : ℝ)) ≤ (148582143 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44243 / 512000)) (148582143 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((18315525083 / 250000) : ℝ) ≤ Real.exp (3 * (3733933 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3733933 / 1000000)) (18315525083 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44227 / 512000) : ℝ) (44243 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3733933 / 1000000) (1867143 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44227 / 512000) (44243 / 512000) (594291427 / 500000000) (148582143 / 125000000) (3733933 / 1000000) (1867143 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44227 / 512000) (44243 / 512000) (3733933 / 1000000) (1867143 / 500000) (33363 / 1000) (4172 / 125)
    (54137 / 1000) (54341 / 1000) (-558413 / 1000) (182691 / 500000) (3111361 / 1000) (109197 / 31250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3733933 / 1000000) (18315525083 / 250000) (109197 / 31250000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3733933 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3733933 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell731 :
    ∀ t ∈ Set.Icc ((44243 / 512000) : ℝ) (44259 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1188657143 / 1000000000) : ℝ) ≤ Real.exp (2 * (44243 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44243 / 512000)) (1188657143 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44259 / 512000) : ℝ)) ≤ (1188731437 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44259 / 512000)) (1188731437 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((73313328413 / 1000000) : ℝ) ≤ Real.exp (3 * (1867083 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1867083 / 500000)) (73313328413 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44243 / 512000) : ℝ) (44259 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1867083 / 500000) (3734519 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44243 / 512000) (44259 / 512000) (1188657143 / 1000000000) (1188731437 / 1000000000) (1867083 / 500000) (3734519 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44243 / 512000) (44259 / 512000) (1867083 / 500000) (3734519 / 1000000) (4171 / 125) (16691 / 500)
    (54167 / 1000) (5437 / 100) (-558449 / 1000) (73039 / 200000) (3112137 / 1000) (1745931 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1867083 / 500000) (73313328413 / 1000000) (1745931 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1867083 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1867083 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell732 :
    ∀ t ∈ Set.Icc ((44259 / 512000) : ℝ) (1771 / 20480), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((297182859 / 250000000) : ℝ) ≤ Real.exp (2 * (44259 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44259 / 512000)) (297182859 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1771 / 20480) : ℝ)) ≤ (237761147 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1771 / 20480)) (237761147 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((18341148079 / 250000) : ℝ) ≤ Real.exp (3 * (3734399 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3734399 / 1000000)) (18341148079 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44259 / 512000) : ℝ) (1771 / 20480),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3734399 / 1000000) (3734753 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44259 / 512000) (1771 / 20480) (297182859 / 250000000) (237761147 / 200000000) (3734399 / 1000000) (3734753 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44259 / 512000) (1771 / 20480) (3734399 / 1000000) (3734753 / 1000000) (16687 / 500) (8347 / 250)
    (13549 / 250) (272 / 5) (-558481 / 1000) (365009 / 1000000) (3112917 / 1000) (1744711 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3734399 / 1000000) (18341148079 / 250000) (1744711 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3734399 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3734399 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell733 :
    ∀ t ∈ Set.Icc ((1771 / 20480) : ℝ) (44291 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((594402867 / 500000000) : ℝ) ≤ Real.exp (2 * (1771 / 20480)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1771 / 20480)) (594402867 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44291 / 512000) : ℝ)) ≤ (594440019 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44291 / 512000)) (594440019 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((9177014039 / 125000) : ℝ) ≤ Real.exp (3 * (3734633 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3734633 / 1000000)) (9177014039 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1771 / 20480) : ℝ) (44291 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3734633 / 1000000) (1867493 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1771 / 20480) (44291 / 512000) (594402867 / 500000000) (594440019 / 500000000) (3734633 / 1000000) (1867493 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1771 / 20480) (44291 / 512000) (3734633 / 1000000) (1867493 / 500000) (1669 / 50) (33393 / 1000)
    (2169 / 40) (54429 / 1000) (-558523 / 1000) (364821 / 1000000) (1556847 / 500) (3486973 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3734633 / 1000000) (9177014039 / 125000) (3486973 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3734633 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3734633 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell734 :
    ∀ t ∈ Set.Icc ((44291 / 512000) : ℝ) (44307 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1188880037 / 1000000000) : ℝ) ≤ Real.exp (2 * (44291 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44291 / 512000)) (1188880037 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44307 / 512000) : ℝ)) ≤ (237790869 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44307 / 512000)) (237790869 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((14693489617 / 200000) : ℝ) ≤ Real.exp (3 * (1867433 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1867433 / 500000)) (14693489617 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44291 / 512000) : ℝ) (44307 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1867433 / 500000) (3735219 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44291 / 512000) (44307 / 512000) (1188880037 / 1000000000) (237790869 / 200000000) (1867433 / 500000) (3735219 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44291 / 512000) (44307 / 512000) (1867433 / 500000) (3735219 / 1000000) (6677 / 200) (33399 / 1000)
    (10851 / 200) (27229 / 500) (-558559 / 1000) (182317 / 500000) (3114471 / 1000) (3484537 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1867433 / 500000) (14693489617 / 200000) (3484537 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1867433 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1867433 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell735 :
    ∀ t ∈ Set.Icc ((44307 / 512000) : ℝ) (44323 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((148619293 / 125000000) : ℝ) ≤ Real.exp (2 * (44307 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44307 / 512000)) (148619293 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44323 / 512000) : ℝ)) ≤ (1189028657 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44323 / 512000)) (1189028657 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((9189880039 / 125000) : ℝ) ≤ Real.exp (3 * (37351 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (37351 / 10000)) (9189880039 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44307 / 512000) : ℝ) (44323 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (37351 / 10000) (3735453 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44307 / 512000) (44323 / 512000) (148619293 / 125000000) (1189028657 / 1000000000) (37351 / 10000) (3735453 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44307 / 512000) (44323 / 512000) (37351 / 10000) (3735453 / 1000000) (33391 / 1000) (8351 / 250)
    (13571 / 250) (6811 / 125) (-139649 / 250) (364447 / 1000000) (778813 / 250) (870523 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (37351 / 10000) (9189880039 / 125000) (870523 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (37351 / 10000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (37351 / 10000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell736 :
    ∀ t ∈ Set.Icc ((44323 / 512000) : ℝ) (44339 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((74314291 / 62500000) : ℝ) ≤ Real.exp (2 * (44323 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44323 / 512000)) (74314291 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44339 / 512000) : ℝ)) ≤ (594551487 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44339 / 512000)) (594551487 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((73570448057 / 1000000) : ℝ) ≤ Real.exp (3 * (3735333 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3735333 / 1000000)) (73570448057 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44323 / 512000) : ℝ) (44339 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3735333 / 1000000) (1867843 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44323 / 512000) (44339 / 512000) (74314291 / 62500000) (594551487 / 500000000) (3735333 / 1000000) (1867843 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44323 / 512000) (44339 / 512000) (3735333 / 1000000) (1867843 / 500000) (8349 / 250) (3341 / 100)
    (54313 / 1000) (54517 / 1000) (-69829 / 125) (364261 / 1000000) (3116029 / 1000) (3479659 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3735333 / 1000000) (73570448057 / 1000000) (3479659 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3735333 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3735333 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell737 :
    ∀ t ∈ Set.Icc ((44339 / 512000) : ℝ) (8871 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1189102973 / 1000000000) : ℝ) ≤ Real.exp (2 * (44339 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44339 / 512000)) (1189102973 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8871 / 102400) : ℝ)) ≤ (237835459 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8871 / 102400)) (237835459 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((18405472937 / 250000) : ℝ) ≤ Real.exp (3 * (1867783 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1867783 / 500000)) (18405472937 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44339 / 512000) : ℝ) (8871 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1867783 / 500000) (46699 / 12500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44339 / 512000) (8871 / 102400) (1189102973 / 1000000000) (237835459 / 200000000) (1867783 / 500000) (46699 / 12500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44339 / 512000) (8871 / 102400) (1867783 / 500000) (46699 / 12500) (16701 / 500) (6683 / 200)
    (27171 / 500) (54547 / 1000) (-69833 / 125) (182037 / 500000) (311681 / 100) (3477227 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1867783 / 500000) (18405472937 / 250000) (3477227 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1867783 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1867783 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell738 :
    ∀ t ∈ Set.Icc ((8871 / 102400) : ℝ) (44371 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((594588647 / 500000000) : ℝ) ≤ Real.exp (2 * (8871 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8871 / 102400)) (594588647 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44371 / 512000) : ℝ)) ≤ (1189251621 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44371 / 512000)) (1189251621 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4604599527 / 62500) : ℝ) ≤ Real.exp (3 * (18679 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (18679 / 5000)) (4604599527 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8871 / 102400) : ℝ) (44371 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (18679 / 5000) (3736153 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8871 / 102400) (44371 / 512000) (594588647 / 500000000) (1189251621 / 1000000000) (18679 / 5000) (3736153 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8871 / 102400) (44371 / 512000) (18679 / 5000) (3736153 / 1000000) (33407 / 1000) (33421 / 1000)
    (13593 / 250) (6822 / 125) (-111741 / 200) (363887 / 1000000) (779397 / 250) (3474787 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (18679 / 5000) (4604599527 / 62500) (3474787 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (18679 / 5000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (18679 / 5000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell739 :
    ∀ t ∈ Set.Icc ((44371 / 512000) : ℝ) (44387 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((59462581 / 50000000) : ℝ) ≤ Real.exp (2 * (44371 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44371 / 512000)) (59462581 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44387 / 512000) : ℝ)) ≤ (1189325951 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44387 / 512000)) (1189325951 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((73725108247 / 1000000) : ℝ) ≤ Real.exp (3 * (3736033 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3736033 / 1000000)) (73725108247 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44371 / 512000) : ℝ) (44387 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3736033 / 1000000) (3736387 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44371 / 512000) (44387 / 512000) (59462581 / 50000000) (1189325951 / 1000000000) (3736033 / 1000000) (3736387 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44371 / 512000) (44387 / 512000) (3736033 / 1000000) (3736387 / 1000000) (33413 / 1000) (33427 / 1000)
    (54401 / 1000) (10921 / 200) (-558737 / 1000) (363701 / 1000000) (3118369 / 1000) (3472359 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3736033 / 1000000) (73725108247 / 1000000) (3472359 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3736033 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3736033 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch036 :
    ∀ t ∈ Set.Icc ((44067 / 512000) : ℝ) (44387 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell720
      hpThetaDensityLowerExpCompact_cell721)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell722
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell723
      hpThetaDensityLowerExpCompact_cell724)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell725
      hpThetaDensityLowerExpCompact_cell726)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell727
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell728
      hpThetaDensityLowerExpCompact_cell729))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell730
      hpThetaDensityLowerExpCompact_cell731)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell732
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell733
      hpThetaDensityLowerExpCompact_cell734)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell735
      hpThetaDensityLowerExpCompact_cell736)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell737
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell738
      hpThetaDensityLowerExpCompact_cell739)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch036
end HodgeProofHP
