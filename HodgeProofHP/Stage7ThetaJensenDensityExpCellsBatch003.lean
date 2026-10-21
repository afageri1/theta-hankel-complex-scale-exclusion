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
theorem hpThetaDensityExpCompact_cell060 :
    ∀ t ∈ Set.Icc ((1701 / 16000) : ℝ) (1703 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((618460359 / 500000000) : ℝ) ≤ Real.exp (2 * (1701 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1701 / 16000)) (618460359 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1703 / 16000) : ℝ)) ≤ (309307497 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1703 / 16000)) (309307497 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((28884573899 / 250000) : ℝ) ≤ Real.exp (3 * (1942893 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1942893 / 500000)) (28884573899 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1701 / 16000) : ℝ) (1703 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1942893 / 500000) (1943441 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1701 / 16000) (1703 / 16000) (618460359 / 500000000) (309307497 / 250000000) (1942893 / 500000) (1943441 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1701 / 16000) (1703 / 16000) (1942893 / 500000) (1943441 / 500000) (9269 / 250) (37117 / 1000)
    (74433 / 1000) (75103 / 1000) (-572317 / 1000) (130633 / 500000) (730391 / 200) (553929 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1942893 / 500000) (28884573899 / 250000) (553929 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1942893 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1942893 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell061 :
    ∀ t ∈ Set.Icc ((1703 / 16000) : ℝ) (341 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1237229987 / 1000000000) : ℝ) ≤ Real.exp (2 * (1703 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1703 / 16000)) (1237229987 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((341 / 3200) : ℝ)) ≤ (618769667 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (341 / 3200)) (618769667 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3621115517 / 31250) : ℝ) ≤ Real.exp (3 * (1943379 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1943379 / 500000)) (3621115517 / 31250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1703 / 16000) : ℝ) (341 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1943379 / 500000) (1943927 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1703 / 16000) (341 / 3200) (1237229987 / 1000000000) (618769667 / 500000000) (1943379 / 500000) (1943927 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1703 / 16000) (341 / 3200) (1943379 / 500000) (1943927 / 500000) (371 / 10) (18571 / 500)
    (74573 / 1000) (18811 / 250) (-114477 / 200) (260701 / 1000000) (365561 / 100) (138079 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1943379 / 500000) (3621115517 / 31250) (138079 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1943379 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1943379 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell062 :
    ∀ t ∈ Set.Icc ((341 / 3200) : ℝ) (1707 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1237539333 / 1000000000) : ℝ) ≤ Real.exp (2 * (341 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (341 / 3200)) (1237539333 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1707 / 16000) : ℝ)) ≤ (618924379 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1707 / 16000)) (618924379 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((23242746829 / 200000) : ℝ) ≤ Real.exp (3 * (3887729 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3887729 / 1000000)) (23242746829 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((341 / 3200) : ℝ) (1707 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3887729 / 1000000) (1944413 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (341 / 3200) (1707 / 16000) (1237539333 / 1000000000) (618924379 / 500000000) (3887729 / 1000000) (1944413 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (341 / 3200) (1707 / 16000) (3887729 / 1000000) (1944413 / 500000) (9281 / 250) (18583 / 500)
    (74713 / 1000) (15077 / 200) (-572447 / 1000) (260137 / 1000000) (3659267 / 1000) (1101419 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3887729 / 1000000) (23242746829 / 200000) (1101419 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3887729 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3887729 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell063 :
    ∀ t ∈ Set.Icc ((1707 / 16000) : ℝ) (1709 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1237848757 / 1000000000) : ℝ) ≤ Real.exp (2 * (1707 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1707 / 16000)) (1237848757 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1709 / 16000) : ℝ)) ≤ (1238158259 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1709 / 16000)) (1238158259 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((5827655377 / 50000) : ℝ) ≤ Real.exp (3 * (3888701 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3888701 / 1000000)) (5827655377 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1707 / 16000) : ℝ) (1709 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3888701 / 1000000) (1944899 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1707 / 16000) (1709 / 16000) (1237848757 / 1000000000) (1238158259 / 1000000000) (3888701 / 1000000) (1944899 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1707 / 16000) (1709 / 16000) (3888701 / 1000000) (1944899 / 500000) (37149 / 1000) (3719 / 100)
    (37427 / 500) (3021 / 40) (-572513 / 1000) (129787 / 500000) (3662927 / 1000) (274553 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3888701 / 1000000) (5827655377 / 50000) (274553 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3888701 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3888701 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell064 :
    ∀ t ∈ Set.Icc ((1709 / 16000) : ℝ) (1711 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((619079129 / 500000000) : ℝ) ≤ Real.exp (2 * (1709 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1709 / 16000)) (619079129 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1711 / 16000) : ℝ)) ≤ (1238467837 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1711 / 16000)) (1238467837 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((11689382267 / 100000) : ℝ) ≤ Real.exp (3 * (1944837 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1944837 / 500000)) (11689382267 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1709 / 16000) : ℝ) (1711 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1944837 / 500000) (3890771 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1709 / 16000) (1711 / 16000) (619079129 / 500000000) (1238467837 / 1000000000) (1944837 / 500000) (3890771 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1709 / 16000) (1711 / 16000) (1944837 / 500000) (3890771 / 1000000) (37173 / 1000) (7443 / 200)
    (37497 / 500) (37833 / 500) (-572579 / 1000) (64753 / 250000) (3666593 / 1000) (1095011 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1944837 / 500000) (11689382267 / 100000) (1095011 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1944837 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1944837 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell065 :
    ∀ t ∈ Set.Icc ((1711 / 16000) : ℝ) (1713 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((309616959 / 250000000) : ℝ) ≤ Real.exp (2 * (1711 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1711 / 16000)) (309616959 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1713 / 16000) : ℝ)) ≤ (1238777493 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1713 / 16000)) (1238777493 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((117235182091 / 1000000) : ℝ) ≤ Real.exp (3 * (1945323 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1945323 / 500000)) (117235182091 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1711 / 16000) : ℝ) (1713 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1945323 / 500000) (121617 / 31250) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1711 / 16000) (1713 / 16000) (309616959 / 250000000) (1238777493 / 1000000000) (1945323 / 500000) (121617 / 31250) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1711 / 16000) (1713 / 16000) (1945323 / 500000) (121617 / 31250) (18599 / 500) (37239 / 1000)
    (15027 / 200) (75807 / 1000) (-14316 / 25) (64613 / 250000) (1835131 / 500) (436729 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1945323 / 500000) (117235182091 / 1000000) (436729 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1945323 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1945323 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell066 :
    ∀ t ∈ Set.Icc ((1713 / 16000) : ℝ) (343 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((309694373 / 250000000) : ℝ) ≤ Real.exp (2 * (1713 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1713 / 16000)) (309694373 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((343 / 3200) : ℝ)) ≤ (619543613 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (343 / 3200)) (619543613 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((58788945549 / 500000) : ℝ) ≤ Real.exp (3 * (3891619 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3891619 / 1000000)) (58788945549 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1713 / 16000) : ℝ) (343 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3891619 / 1000000) (3892717 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1713 / 16000) (343 / 3200) (309694373 / 250000000) (619543613 / 500000000) (3891619 / 1000000) (3892717 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1713 / 16000) (343 / 3200) (3891619 / 1000000) (3892717 / 1000000) (18611 / 500) (4658 / 125)
    (18819 / 250) (75949 / 1000) (-71588 / 125) (64473 / 250000) (1836967 / 500) (2177281 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3891619 / 1000000) (58788945549 / 500000) (2177281 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3891619 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3891619 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell067 :
    ∀ t ∈ Set.Icc ((343 / 3200) : ℝ) (1717 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((49563489 / 40000000) : ℝ) ≤ Real.exp (2 * (343 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (343 / 3200)) (49563489 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1717 / 16000) : ℝ)) ≤ (309849259 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1717 / 16000)) (309849259 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((117921601931 / 1000000) : ℝ) ≤ Real.exp (3 * (243287 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (243287 / 62500)) (117921601931 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((343 / 3200) : ℝ) (1717 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (243287 / 62500) (389369 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (343 / 3200) (1717 / 16000) (49563489 / 40000000) (309849259 / 250000000) (243287 / 62500) (389369 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (343 / 3200) (1717 / 16000) (243287 / 62500) (389369 / 100000) (18623 / 500) (4661 / 125)
    (75417 / 1000) (7609 / 100) (-572769 / 1000) (257333 / 1000000) (3677609 / 1000) (1085467 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (243287 / 62500) (117921601931 / 1000000) (1085467 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (243287 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (243287 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell068 :
    ∀ t ∈ Set.Icc ((1717 / 16000) : ℝ) (1719 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((247879407 / 200000000) : ℝ) ≤ Real.exp (2 * (1717 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1717 / 16000)) (247879407 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1719 / 16000) : ℝ)) ≤ (309926731 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1719 / 16000)) (309926731 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((59133158759 / 500000) : ℝ) ≤ Real.exp (3 * (778713 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (778713 / 200000)) (59133158759 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1717 / 16000) : ℝ) (1719 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (778713 / 200000) (486833 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1717 / 16000) (1719 / 16000) (247879407 / 200000000) (309926731 / 250000000) (778713 / 200000) (486833 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1717 / 16000) (1719 / 16000) (778713 / 200000) (486833 / 125000) (37271 / 1000) (37313 / 1000)
    (37779 / 500) (9529 / 125) (-572827 / 1000) (32097 / 125000) (368129 / 100) (2164607 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (778713 / 200000) (59133158759 / 500000) (2164607 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (778713 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (778713 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell069 :
    ∀ t ∈ Set.Icc ((1719 / 16000) : ℝ) (1721 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1239706923 / 1000000000) : ℝ) ≤ Real.exp (2 * (1719 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1719 / 16000)) (1239706923 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1721 / 16000) : ℝ)) ≤ (124001689 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1721 / 16000)) (124001689 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((118612396633 / 1000000) : ℝ) ≤ Real.exp (3 * (3894539 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3894539 / 1000000)) (118612396633 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1719 / 16000) : ℝ) (1721 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3894539 / 1000000) (1947819 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1719 / 16000) (1721 / 16000) (1239706923 / 1000000000) (124001689 / 100000000) (3894539 / 1000000) (1947819 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1719 / 16000) (1721 / 16000) (3894539 / 1000000) (1947819 / 500000) (7459 / 200) (37337 / 1000)
    (75699 / 1000) (38187 / 500) (-57289 / 100) (128109 / 500000) (1842487 / 500) (2158291 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3894539 / 1000000) (118612396633 / 1000000) (2158291 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3894539 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3894539 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell070 :
    ∀ t ∈ Set.Icc ((1721 / 16000) : ℝ) (1723 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1240016889 / 1000000000) : ℝ) ≤ Real.exp (2 * (1721 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1721 / 16000)) (1240016889 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1723 / 16000) : ℝ)) ≤ (1240326933 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1723 / 16000)) (1240326933 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((59479744233 / 500000) : ℝ) ≤ Real.exp (3 * (3895513 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3895513 / 1000000)) (59479744233 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1721 / 16000) : ℝ) (1723 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3895513 / 1000000) (974153 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1721 / 16000) (1723 / 16000) (1240016889 / 1000000000) (1240326933 / 1000000000) (3895513 / 1000000) (974153 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1721 / 16000) (1723 / 16000) (3895513 / 1000000) (974153 / 250000) (933 / 25) (18681 / 500)
    (75841 / 1000) (15303 / 200) (-572953 / 1000) (255663 / 1000000) (3688661 / 1000) (1075997 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3895513 / 1000000) (59479744233 / 500000) (1075997 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3895513 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3895513 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell071 :
    ∀ t ∈ Set.Icc ((1723 / 16000) : ℝ) (69 / 640), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((310081733 / 250000000) : ℝ) ≤ Real.exp (2 * (1723 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1723 / 16000)) (310081733 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((69 / 640) : ℝ)) ≤ (1240637053 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (69 / 640)) (1240637053 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((119307595981 / 1000000) : ℝ) ≤ Real.exp (3 * (3896487 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3896487 / 1000000)) (119307595981 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1723 / 16000) : ℝ) (69 / 640),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3896487 / 1000000) (1948793 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1723 / 16000) (69 / 640) (310081733 / 250000000) (1240637053 / 1000000000) (3896487 / 1000000) (1948793 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1723 / 16000) (69 / 640) (3896487 / 1000000) (1948793 / 500000) (4668 / 125) (18693 / 500)
    (37991 / 500) (76657 / 1000) (-114603 / 200) (63777 / 250000) (73847 / 20) (429143 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3896487 / 1000000) (119307595981 / 1000000) (429143 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3896487 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3896487 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell072 :
    ∀ t ∈ Set.Icc ((69 / 640) : ℝ) (1727 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((310159263 / 250000000) : ℝ) ≤ Real.exp (2 * (69 / 640)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (69 / 640)) (310159263 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1727 / 16000) : ℝ)) ≤ (1240947251 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1727 / 16000)) (1240947251 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((119656722151 / 1000000) : ℝ) ≤ Real.exp (3 * (3897461 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3897461 / 1000000)) (119656722151 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((69 / 640) : ℝ) (1727 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3897461 / 1000000) (12183 / 3125) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (69 / 640) (1727 / 16000) (310159263 / 250000000) (1240947251 / 1000000000) (3897461 / 1000000) (12183 / 3125) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (69 / 640) (1727 / 16000) (3897461 / 1000000) (12183 / 3125) (37369 / 1000) (37411 / 1000)
    (19031 / 250) (76799 / 1000) (-143269 / 250) (127277 / 500000) (1848021 / 500) (1069727 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3897461 / 1000000) (119656722151 / 1000000) (1069727 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3897461 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3897461 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell073 :
    ∀ t ∈ Set.Icc ((1727 / 16000) : ℝ) (1729 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((4963789 / 4000000) : ℝ) ≤ Real.exp (2 * (1727 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1727 / 16000)) (4963789 / 4000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1729 / 16000) : ℝ)) ≤ (1241257527 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1729 / 16000)) (1241257527 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((30001717489 / 250000) : ℝ) ≤ Real.exp (3 * (779687 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (779687 / 200000)) (30001717489 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1727 / 16000) : ℝ) (1729 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (779687 / 200000) (779907 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1727 / 16000) (1729 / 16000) (4963789 / 4000000) (1241257527 / 1000000000) (779687 / 200000) (779907 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1727 / 16000) (1729 / 16000) (779687 / 200000) (779907 / 200000) (37393 / 1000) (7487 / 200)
    (38133 / 500) (38471 / 500) (-143283 / 250) (127001 / 500000) (3699741 / 1000) (533303 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (779687 / 200000) (30001717489 / 250000) (533303 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (779687 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (779687 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell074 :
    ∀ t ∈ Set.Icc ((1729 / 16000) : ℝ) (1731 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((620628763 / 500000000) : ℝ) ≤ Real.exp (2 * (1729 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1729 / 16000)) (620628763 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1731 / 16000) : ℝ)) ≤ (31039197 / 25000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1731 / 16000)) (31039197 / 25000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((120358403459 / 1000000) : ℝ) ≤ Real.exp (3 * (389941 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (389941 / 100000)) (120358403459 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1729 / 16000) : ℝ) (1731 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (389941 / 100000) (390051 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1729 / 16000) (1731 / 16000) (620628763 / 500000000) (31039197 / 25000000) (389941 / 100000) (390051 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1729 / 16000) (1731 / 16000) (389941 / 100000) (390051 / 100000) (18709 / 500) (1873 / 50)
    (9551 / 125) (19271 / 250) (-71649 / 125) (5069 / 20000) (3703443 / 1000) (2126981 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (389941 / 100000) (120358403459 / 1000000) (2126981 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (389941 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (389941 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell075 :
    ∀ t ∈ Set.Icc ((1731 / 16000) : ℝ) (1733 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1241567879 / 1000000000) : ℝ) ≤ Real.exp (2 * (1731 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1731 / 16000)) (1241567879 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1733 / 16000) : ℝ)) ≤ (1241878311 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1733 / 16000)) (1241878311 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1207109667 / 10000) : ℝ) ≤ Real.exp (3 * (780077 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (780077 / 200000)) (1207109667 / 10000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1731 / 16000) : ℝ) (1733 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (780077 / 200000) (780297 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1731 / 16000) (1733 / 16000) (1241567879 / 1000000000) (1241878311 / 1000000000) (780077 / 200000) (780297 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1731 / 16000) (1733 / 16000) (780077 / 200000) (780297 / 200000) (37443 / 1000) (7497 / 200)
    (1531 / 20) (77227 / 1000) (-143313 / 250) (252899 / 1000000) (3707147 / 1000) (2120769 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (780077 / 200000) (1207109667 / 10000) (2120769 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (780077 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (780077 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell076 :
    ∀ t ∈ Set.Icc ((1733 / 16000) : ℝ) (347 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((124187831 / 100000000) : ℝ) ≤ Real.exp (2 * (1733 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1733 / 16000)) (124187831 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((347 / 3200) : ℝ)) ≤ (1242188819 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (347 / 3200)) (1242188819 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((60532281347 / 500000) : ℝ) ≤ Real.exp (3 * (48767 / 12500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (48767 / 12500)) (60532281347 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1733 / 16000) : ℝ) (347 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (48767 / 12500) (3902461 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1733 / 16000) (347 / 3200) (124187831 / 100000000) (1242188819 / 1000000000) (48767 / 12500) (3902461 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1733 / 16000) (347 / 3200) (48767 / 12500) (3902461 / 1000000) (37467 / 1000) (37509 / 1000)
    (19173 / 250) (7737 / 100) (-286653 / 500) (5047 / 20000) (1855429 / 500) (84583 / 40000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (48767 / 12500) (60532281347 / 500000) (84583 / 40000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (48767 / 12500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (48767 / 12500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell077 :
    ∀ t ∈ Set.Icc ((347 / 3200) : ℝ) (1737 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((621094409 / 500000000) : ℝ) ≤ Real.exp (2 * (347 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (347 / 3200)) (621094409 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1737 / 16000) : ℝ)) ≤ (248499881 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1737 / 16000)) (248499881 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((30354889681 / 250000) : ℝ) ≤ Real.exp (3 * (60974 / 15625)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (60974 / 15625)) (30354889681 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((347 / 3200) : ℝ) (1737 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (60974 / 15625) (3903437 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (347 / 3200) (1737 / 16000) (621094409 / 500000000) (248499881 / 200000000) (60974 / 15625) (3903437 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (347 / 3200) (1737 / 16000) (60974 / 15625) (3903437 / 1000000) (9373 / 250) (18767 / 500)
    (15367 / 200) (77513 / 1000) (-143341 / 250) (251801 / 1000000) (928643 / 250) (263549 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (60974 / 15625) (30354889681 / 250000) (263549 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (60974 / 15625)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (60974 / 15625)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell078 :
    ∀ t ∈ Set.Icc ((1737 / 16000) : ℝ) (1739 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((310624851 / 250000000) : ℝ) ≤ Real.exp (2 * (1737 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1737 / 16000)) (310624851 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1739 / 16000) : ℝ)) ≤ (1242810069 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1739 / 16000)) (1242810069 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((121775230377 / 1000000) : ℝ) ≤ Real.exp (3 * (3903311 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3903311 / 1000000)) (121775230377 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1737 / 16000) : ℝ) (1739 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3903311 / 1000000) (3904413 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1737 / 16000) (1739 / 16000) (310624851 / 250000000) (1242810069 / 1000000000) (3903311 / 1000000) (3904413 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1737 / 16000) (1739 / 16000) (3903311 / 1000000) (3904413 / 1000000) (9379 / 250) (18779 / 500)
    (38489 / 500) (9707 / 125) (-573417 / 1000) (125627 / 500000) (464786 / 125) (1051117 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3903311 / 1000000) (121775230377 / 1000000) (1051117 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3903311 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3903311 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell079 :
    ∀ t ∈ Set.Icc ((1739 / 16000) : ℝ) (1741 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((310702517 / 250000000) : ℝ) ≤ Real.exp (2 * (1739 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1739 / 16000)) (310702517 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1741 / 16000) : ℝ)) ≤ (124312081 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1741 / 16000)) (124312081 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((24426462057 / 200000) : ℝ) ≤ Real.exp (3 * (3904287 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3904287 / 1000000)) (24426462057 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1739 / 16000) : ℝ) (1741 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3904287 / 1000000) (3905389 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1739 / 16000) (1741 / 16000) (310702517 / 250000000) (124312081 / 100000000) (3904287 / 1000000) (3905389 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1739 / 16000) (1741 / 16000) (3904287 / 1000000) (3905389 / 1000000) (37541 / 1000) (37583 / 1000)
    (77121 / 1000) (389 / 5) (-286737 / 500) (250707 / 1000000) (3722007 / 1000) (262011 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3904287 / 1000000) (24426462057 / 200000) (262011 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3904287 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3904287 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityExpCompact_cellsBatch003 :
    ∀ t ∈ Set.Icc ((1701 / 16000) : ℝ) (1741 / 16000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell060
      hpThetaDensityExpCompact_cell061)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell062
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell063
      hpThetaDensityExpCompact_cell064)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell065
      hpThetaDensityExpCompact_cell066)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell067
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell068
      hpThetaDensityExpCompact_cell069))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell070
      hpThetaDensityExpCompact_cell071)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell072
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell073
      hpThetaDensityExpCompact_cell074)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell075
      hpThetaDensityExpCompact_cell076)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell077
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell078
      hpThetaDensityExpCompact_cell079)))))

#print axioms hpThetaDensityExpCompact_cellsBatch003
end HodgeProofHP
