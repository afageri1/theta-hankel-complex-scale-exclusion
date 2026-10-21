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
theorem hpThetaDensityLowerExpCompact_cell260 :
    ∀ t ∈ Set.Icc ((41327 / 512000) : ℝ) (41329 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((235038883 / 200000000) : ℝ) ≤ Real.exp (2 * (41327 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41327 / 512000)) (235038883 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41329 / 512000) : ℝ)) ≤ (1175203597 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41329 / 512000)) (1175203597 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64577334479 / 1000000) : ℝ) ≤ Real.exp (3 * (3691873 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3691873 / 1000000)) (64577334479 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41327 / 512000) : ℝ) (41329 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3691873 / 1000000) (184601 / 50000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41327 / 512000) (41329 / 512000) (235038883 / 200000000) (1175203597 / 1000000000) (3691873 / 1000000) (184601 / 50000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41327 / 512000) (41329 / 512000) (3691873 / 1000000) (184601 / 50000) (32367 / 1000) (32373 / 1000)
    (49007 / 1000) (49091 / 1000) (-552291 / 1000) (80121 / 200000) (371609 / 125) (49553 / 12500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3691873 / 1000000) (64577334479 / 1000000) (49553 / 12500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3691873 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3691873 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell261 :
    ∀ t ∈ Set.Icc ((41329 / 512000) : ℝ) (41331 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((293800899 / 250000000) : ℝ) ≤ Real.exp (2 * (41329 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41329 / 512000)) (293800899 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41331 / 512000) : ℝ)) ≤ (587606389 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41331 / 512000)) (587606389 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64582952949 / 1000000) : ℝ) ≤ Real.exp (3 * (1845951 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1845951 / 500000)) (64582952949 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41329 / 512000) : ℝ) (41331 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1845951 / 500000) (3692049 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41329 / 512000) (41331 / 512000) (293800899 / 250000000) (587606389 / 500000000) (1845951 / 500000) (3692049 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41329 / 512000) (41331 / 512000) (1845951 / 500000) (3692049 / 1000000) (4046 / 125) (16187 / 500)
    (4901 / 100) (24547 / 500) (-69037 / 125) (20029 / 50000) (1486483 / 500) (792779 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1845951 / 500000) (64582952949 / 1000000) (792779 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1845951 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1845951 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell262 :
    ∀ t ∈ Set.Icc ((41331 / 512000) : ℝ) (41333 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175212777 / 1000000000) : ℝ) ≤ Real.exp (2 * (41331 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41331 / 512000)) (1175212777 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41333 / 512000) : ℝ)) ≤ (29380549 / 25000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41333 / 512000)) (29380549 / 25000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64588378143 / 1000000) : ℝ) ≤ Real.exp (3 * (369193 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (369193 / 100000)) (64588378143 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41331 / 512000) : ℝ) (41333 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (369193 / 100000) (1846039 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41331 / 512000) (41333 / 512000) (1175212777 / 1000000000) (29380549 / 25000000) (369193 / 100000) (1846039 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41331 / 512000) (41333 / 512000) (369193 / 100000) (1846039 / 500000) (4046 / 125) (259 / 8)
    (24507 / 500) (24549 / 500) (-552297 / 1000) (80111 / 200000) (2973059 / 1000) (1981781 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (369193 / 100000) (64588378143 / 1000000) (1981781 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (369193 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (369193 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell263 :
    ∀ t ∈ Set.Icc ((41333 / 512000) : ℝ) (8267 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175221959 / 1000000000) : ℝ) ≤ Real.exp (2 * (41333 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41333 / 512000)) (1175221959 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8267 / 102400) : ℝ)) ≤ (1175231141 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8267 / 102400)) (1175231141 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64593997573 / 1000000) : ℝ) ≤ Real.exp (3 * (3691959 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3691959 / 1000000)) (64593997573 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41333 / 512000) : ℝ) (8267 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3691959 / 1000000) (3692107 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41333 / 512000) (8267 / 102400) (1175221959 / 1000000000) (1175231141 / 1000000000) (3691959 / 1000000) (3692107 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41333 / 512000) (8267 / 102400) (3691959 / 1000000) (3692107 / 1000000) (32369 / 1000) (259 / 8)
    (49017 / 1000) (49101 / 1000) (-276151 / 500) (40053 / 100000) (371644 / 125) (3963217 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3691959 / 1000000) (64593997573 / 1000000) (3963217 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3691959 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3691959 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell264 :
    ∀ t ∈ Set.Icc ((8267 / 102400) : ℝ) (41337 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((58761557 / 50000000) : ℝ) ≤ Real.exp (2 * (8267 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8267 / 102400)) (58761557 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41337 / 512000) : ℝ)) ≤ (1175240323 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41337 / 512000)) (1175240323 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64599617493 / 1000000) : ℝ) ≤ Real.exp (3 * (922997 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (922997 / 250000)) (64599617493 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8267 / 102400) : ℝ) (41337 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (922997 / 250000) (738427 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8267 / 102400) (41337 / 512000) (58761557 / 50000000) (1175240323 / 1000000000) (922997 / 250000) (738427 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8267 / 102400) (41337 / 512000) (922997 / 250000) (738427 / 200000) (3237 / 100) (4047 / 125)
    (49021 / 1000) (9821 / 200) (-69039 / 125) (50063 / 125000) (2973243 / 1000) (495359 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (922997 / 250000) (64599617493 / 1000000) (495359 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922997 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922997 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell265 :
    ∀ t ∈ Set.Icc ((41337 / 512000) : ℝ) (41339 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587620161 / 500000000) : ℝ) ≤ Real.exp (2 * (41337 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41337 / 512000)) (587620161 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41339 / 512000) : ℝ)) ≤ (36726547 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41339 / 512000)) (36726547 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32302618951 / 500000) : ℝ) ≤ Real.exp (3 * (3692017 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3692017 / 1000000)) (32302618951 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41337 / 512000) : ℝ) (41339 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3692017 / 1000000) (923041 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41337 / 512000) (41339 / 512000) (587620161 / 500000000) (36726547 / 31250000) (3692017 / 1000000) (923041 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41337 / 512000) (41339 / 512000) (3692017 / 1000000) (923041 / 250000) (3237 / 100) (32377 / 1000)
    (6128 / 125) (12277 / 250) (-552317 / 1000) (400479 / 1000000) (371667 / 125) (123829 / 31250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3692017 / 1000000) (32302618951 / 500000) (123829 / 31250000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3692017 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3692017 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell266 :
    ∀ t ∈ Set.Icc ((41339 / 512000) : ℝ) (41341 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175249503 / 1000000000) : ℝ) ≤ Real.exp (2 * (41339 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41339 / 512000)) (1175249503 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41341 / 512000) : ℝ)) ≤ (587629343 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41341 / 512000)) (587629343 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64610858799 / 1000000) : ℝ) ≤ Real.exp (3 * (1846023 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1846023 / 500000)) (64610858799 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41339 / 512000) : ℝ) (41341 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1846023 / 500000) (3692193 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41339 / 512000) (41341 / 512000) (1175249503 / 1000000000) (587629343 / 500000000) (1846023 / 500000) (3692193 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41339 / 512000) (41341 / 512000) (1846023 / 500000) (3692193 / 1000000) (32371 / 1000) (32377 / 1000)
    (12257 / 250) (6139 / 125) (-276161 / 500) (400453 / 1000000) (2973429 / 1000) (3962183 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1846023 / 500000) (64610858799 / 1000000) (3962183 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1846023 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1846023 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell267 :
    ∀ t ∈ Set.Icc ((41341 / 512000) : ℝ) (41343 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((235051737 / 200000000) : ℝ) ≤ Real.exp (2 * (41341 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41341 / 512000)) (235051737 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41343 / 512000) : ℝ)) ≤ (293816967 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41343 / 512000)) (293816967 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32308240093 / 500000) : ℝ) ≤ Real.exp (3 * (147683 / 40000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (147683 / 40000)) (32308240093 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41341 / 512000) : ℝ) (41343 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (147683 / 40000) (1846111 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41341 / 512000) (41343 / 512000) (235051737 / 200000000) (293816967 / 250000000) (147683 / 40000) (1846111 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41341 / 512000) (41343 / 512000) (147683 / 40000) (1846111 / 500000) (8093 / 250) (16189 / 500)
    (49031 / 1000) (9823 / 200) (-552327 / 1000) (100107 / 250000) (2973523 / 1000) (1980919 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (147683 / 40000) (32308240093 / 500000) (1980919 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (147683 / 40000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (147683 / 40000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell268 :
    ∀ t ∈ Set.Icc ((41343 / 512000) : ℝ) (8269 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175267867 / 1000000000) : ℝ) ≤ Real.exp (2 * (41343 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41343 / 512000)) (1175267867 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8269 / 102400) : ℝ)) ≤ (23505541 / 20000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8269 / 102400)) (23505541 / 20000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32311051031 / 500000) : ℝ) ≤ Real.exp (3 * (461513 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (461513 / 125000)) (32311051031 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41343 / 512000) : ℝ) (8269 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (461513 / 125000) (3692251 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41343 / 512000) (8269 / 102400) (1175267867 / 1000000000) (23505541 / 20000000) (461513 / 125000) (3692251 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41343 / 512000) (8269 / 102400) (461513 / 125000) (3692251 / 1000000) (32373 / 1000) (32379 / 1000)
    (9807 / 200) (49119 / 1000) (-138083 / 250) (400403 / 1000000) (371702 / 125) (3961493 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (461513 / 125000) (32311051031 / 500000) (3961493 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461513 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461513 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell269 :
    ∀ t ∈ Set.Icc ((8269 / 102400) : ℝ) (41347 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175277049 / 1000000000) : ℝ) ≤ Real.exp (2 * (8269 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8269 / 102400)) (1175277049 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41347 / 512000) : ℝ)) ≤ (1175286231 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41347 / 512000)) (1175286231 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4039220659 / 62500) : ℝ) ≤ Real.exp (3 * (923033 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (923033 / 250000)) (4039220659 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8269 / 102400) : ℝ) (41347 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (923033 / 250000) (92307 / 25000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8269 / 102400) (41347 / 512000) (1175277049 / 1000000000) (1175286231 / 1000000000) (923033 / 250000) (92307 / 25000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8269 / 102400) (41347 / 512000) (923033 / 250000) (92307 / 25000) (32373 / 1000) (32379 / 1000)
    (24519 / 500) (24561 / 500) (-552333 / 1000) (200189 / 500000) (297371 / 100) (3961161 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (923033 / 250000) (4039220659 / 62500) (3961161 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (923033 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (923033 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell270 :
    ∀ t ∈ Set.Icc ((41347 / 512000) : ℝ) (41349 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((117528623 / 100000000) : ℝ) ≤ Real.exp (2 * (41347 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41347 / 512000)) (117528623 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41349 / 512000) : ℝ)) ≤ (1175295413 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41349 / 512000)) (1175295413 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64633153381 / 1000000) : ℝ) ≤ Real.exp (3 * (3692161 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3692161 / 1000000)) (64633153381 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41347 / 512000) : ℝ) (41349 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3692161 / 1000000) (3692309 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41347 / 512000) (41349 / 512000) (117528623 / 100000000) (1175295413 / 1000000000) (3692161 / 1000000) (3692309 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41347 / 512000) (41349 / 512000) (3692161 / 1000000) (3692309 / 1000000) (16187 / 500) (1619 / 50)
    (49041 / 1000) (24563 / 500) (-276169 / 500) (400353 / 1000000) (2973803 / 1000) (247551 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3692161 / 1000000) (64633153381 / 1000000) (247551 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3692161 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3692161 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell271 :
    ∀ t ∈ Set.Icc ((41349 / 512000) : ℝ) (41351 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((293823853 / 250000000) : ℝ) ≤ Real.exp (2 * (41349 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41349 / 512000)) (293823853 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41351 / 512000) : ℝ)) ≤ (235060919 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41351 / 512000)) (235060919 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16159694177 / 250000) : ℝ) ≤ Real.exp (3 * (369219 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (369219 / 100000)) (16159694177 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41349 / 512000) : ℝ) (41351 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (369219 / 100000) (3692337 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41349 / 512000) (41351 / 512000) (293823853 / 250000000) (235060919 / 200000000) (369219 / 100000) (3692337 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41349 / 512000) (41351 / 512000) (369219 / 100000) (3692337 / 1000000) (259 / 8) (32381 / 1000)
    (9809 / 200) (49129 / 1000) (-138087 / 250) (400327 / 1000000) (2973893 / 1000) (3960471 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (369219 / 100000) (16159694177 / 250000) (3960471 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (369219 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (369219 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell272 :
    ∀ t ∈ Set.Icc ((41351 / 512000) : ℝ) (41353 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587652297 / 500000000) : ℝ) ≤ Real.exp (2 * (41351 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41351 / 512000)) (587652297 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41353 / 512000) : ℝ)) ≤ (587656889 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41353 / 512000)) (587656889 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64644400523 / 1000000) : ℝ) ≤ Real.exp (3 * (3692219 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3692219 / 1000000)) (64644400523 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41351 / 512000) : ℝ) (41353 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3692219 / 1000000) (1846183 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41351 / 512000) (41353 / 512000) (587652297 / 500000000) (587656889 / 500000000) (3692219 / 1000000) (1846183 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41351 / 512000) (41353 / 512000) (3692219 / 1000000) (1846183 / 500000) (259 / 8) (32381 / 1000)
    (49049 / 1000) (49133 / 1000) (-552353 / 1000) (200151 / 500000) (2973987 / 1000) (3960127 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3692219 / 1000000) (64644400523 / 1000000) (3960127 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3692219 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3692219 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell273 :
    ∀ t ∈ Set.Icc ((41353 / 512000) : ℝ) (8271 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175313777 / 1000000000) : ℝ) ≤ Real.exp (2 * (41353 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41353 / 512000)) (1175313777 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8271 / 102400) : ℝ)) ≤ (14691537 / 12500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8271 / 102400)) (14691537 / 12500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16162506207 / 250000) : ℝ) ≤ Real.exp (3 * (461531 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (461531 / 125000)) (16162506207 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41353 / 512000) : ℝ) (8271 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (461531 / 125000) (738479 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41353 / 512000) (8271 / 102400) (1175313777 / 1000000000) (14691537 / 12500000) (461531 / 125000) (738479 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41353 / 512000) (8271 / 102400) (461531 / 125000) (738479 / 200000) (4047 / 125) (16191 / 500)
    (12263 / 250) (6142 / 125) (-276179 / 500) (100069 / 250000) (74352 / 25) (1979891 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (461531 / 125000) (16162506207 / 250000) (1979891 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461531 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461531 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell274 :
    ∀ t ∈ Set.Icc ((8271 / 102400) : ℝ) (41357 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175322959 / 1000000000) : ℝ) ≤ Real.exp (2 * (8271 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8271 / 102400)) (1175322959 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41357 / 512000) : ℝ)) ≤ (587666071 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41357 / 512000)) (587666071 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64655649623 / 1000000) : ℝ) ≤ Real.exp (3 * (3692277 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3692277 / 1000000)) (64655649623 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8271 / 102400) : ℝ) (41357 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3692277 / 1000000) (461553 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8271 / 102400) (41357 / 512000) (1175322959 / 1000000000) (587666071 / 500000000) (3692277 / 1000000) (461553 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8271 / 102400) (41357 / 512000) (3692277 / 1000000) (461553 / 125000) (32377 / 1000) (32383 / 1000)
    (6132 / 125) (49139 / 1000) (-552363 / 1000) (400251 / 1000000) (1487087 / 500) (1979719 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3692277 / 1000000) (64655649623 / 1000000) (1979719 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3692277 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3692277 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell275 :
    ∀ t ∈ Set.Icc ((41357 / 512000) : ℝ) (41359 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175332141 / 1000000000) : ℝ) ≤ Real.exp (2 * (41357 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41357 / 512000)) (1175332141 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41359 / 512000) : ℝ)) ≤ (293835331 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41359 / 512000)) (293835331 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64661080923 / 1000000) : ℝ) ≤ Real.exp (3 * (738461 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (738461 / 200000)) (64661080923 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41357 / 512000) : ℝ) (41359 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (738461 / 200000) (3692453 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41357 / 512000) (41359 / 512000) (1175332141 / 1000000000) (293835331 / 250000000) (738461 / 200000) (3692453 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41357 / 512000) (41359 / 512000) (738461 / 200000) (3692453 / 1000000) (32377 / 1000) (4048 / 125)
    (49059 / 1000) (49143 / 1000) (-138091 / 250) (400227 / 1000000) (2974267 / 1000) (791821 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (738461 / 200000) (64661080923 / 1000000) (791821 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (738461 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (738461 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell276 :
    ∀ t ∈ Set.Icc ((41359 / 512000) : ℝ) (41361 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175341323 / 1000000000) : ℝ) ≤ Real.exp (2 * (41359 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41359 / 512000)) (1175341323 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41361 / 512000) : ℝ)) ≤ (1175350507 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41361 / 512000)) (1175350507 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64666706679 / 1000000) : ℝ) ≤ Real.exp (3 * (1846167 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1846167 / 500000)) (64666706679 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41359 / 512000) : ℝ) (41361 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1846167 / 500000) (1846241 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41359 / 512000) (41361 / 512000) (1175341323 / 1000000000) (1175350507 / 1000000000) (1846167 / 500000) (1846241 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41359 / 512000) (41361 / 512000) (1846167 / 500000) (1846241 / 500000) (16189 / 500) (4048 / 125)
    (24531 / 500) (49147 / 1000) (-552369 / 1000) (400201 / 1000000) (74359 / 25) (3958761 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1846167 / 500000) (64666706679 / 1000000) (3958761 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1846167 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1846167 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell277 :
    ∀ t ∈ Set.Icc ((41361 / 512000) : ℝ) (41363 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587675253 / 500000000) : ℝ) ≤ Real.exp (2 * (41361 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41361 / 512000)) (587675253 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41363 / 512000) : ℝ)) ≤ (1175359689 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41363 / 512000)) (1175359689 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2586893317 / 40000) : ℝ) ≤ Real.exp (3 * (3692363 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3692363 / 1000000)) (2586893317 / 40000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41361 / 512000) : ℝ) (41363 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3692363 / 1000000) (369251 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41361 / 512000) (41363 / 512000) (587675253 / 500000000) (1175359689 / 1000000000) (3692363 / 1000000) (369251 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41361 / 512000) (41363 / 512000) (3692363 / 1000000) (369251 / 100000) (32379 / 1000) (6477 / 200)
    (24533 / 500) (983 / 20) (-276189 / 500) (25011 / 62500) (2974451 / 1000) (3958417 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3692363 / 1000000) (2586893317 / 40000) (3958417 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3692363 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3692363 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell278 :
    ∀ t ∈ Set.Icc ((41363 / 512000) : ℝ) (8273 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((146919961 / 125000000) : ℝ) ≤ Real.exp (2 * (41363 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41363 / 512000)) (146919961 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8273 / 102400) : ℝ)) ≤ (146921109 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8273 / 102400)) (146921109 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3233897983 / 50000) : ℝ) ≤ Real.exp (3 * (461549 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (461549 / 125000)) (3233897983 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41363 / 512000) : ℝ) (8273 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (461549 / 125000) (3692539 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41363 / 512000) (8273 / 102400) (146919961 / 125000000) (146921109 / 125000000) (461549 / 125000) (3692539 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41363 / 512000) (8273 / 102400) (461549 / 125000) (3692539 / 1000000) (32379 / 1000) (16193 / 500)
    (4907 / 100) (49153 / 1000) (-69048 / 125) (8003 / 20000) (371818 / 125) (494759 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (461549 / 125000) (3233897983 / 50000) (494759 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461549 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461549 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell279 :
    ∀ t ∈ Set.Icc ((8273 / 102400) : ℝ) (41367 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1175368871 / 1000000000) : ℝ) ≤ Real.exp (2 * (8273 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8273 / 102400)) (1175368871 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41367 / 512000) : ℝ)) ≤ (587689027 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41367 / 512000)) (587689027 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((12936717377 / 200000) : ℝ) ≤ Real.exp (3 * (3692421 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3692421 / 1000000)) (12936717377 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8273 / 102400) : ℝ) (41367 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3692421 / 1000000) (461571 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8273 / 102400) (41367 / 512000) (1175368871 / 1000000000) (587689027 / 500000000) (3692421 / 1000000) (461571 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8273 / 102400) (41367 / 512000) (3692421 / 1000000) (461571 / 125000) (1619 / 50) (16193 / 500)
    (49073 / 1000) (49157 / 1000) (-552389 / 1000) (3201 / 8000) (1487319 / 500) (123679 / 31250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3692421 / 1000000) (12936717377 / 200000) (123679 / 31250000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3692421 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3692421 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch013 :
    ∀ t ∈ Set.Icc ((41327 / 512000) : ℝ) (41367 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell260
      hpThetaDensityLowerExpCompact_cell261)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell262
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell263
      hpThetaDensityLowerExpCompact_cell264)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell265
      hpThetaDensityLowerExpCompact_cell266)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell267
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell268
      hpThetaDensityLowerExpCompact_cell269))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell270
      hpThetaDensityLowerExpCompact_cell271)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell272
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell273
      hpThetaDensityLowerExpCompact_cell274)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell275
      hpThetaDensityLowerExpCompact_cell276)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell277
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell278
      hpThetaDensityLowerExpCompact_cell279)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch013
end HodgeProofHP
