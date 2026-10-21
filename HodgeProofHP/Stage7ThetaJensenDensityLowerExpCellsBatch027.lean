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
theorem hpThetaDensityLowerExpCompact_cell540 :
    ∀ t ∈ Set.Icc ((42403 / 512000) : ℝ) (42411 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1180144299 / 1000000000) : ℝ) ≤ Real.exp (2 * (42403 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42403 / 512000)) (1180144299 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42411 / 512000) : ℝ)) ≤ (59009059 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42411 / 512000)) (59009059 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((13532247701 / 200000) : ℝ) ≤ Real.exp (3 * (3707423 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3707423 / 1000000)) (13532247701 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42403 / 512000) : ℝ) (42411 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3707423 / 1000000) (1853829 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42403 / 512000) (42411 / 512000) (1180144299 / 1000000000) (59009059 / 50000000) (3707423 / 1000000) (1853829 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42403 / 512000) (42411 / 512000) (3707423 / 1000000) (1853829 / 500000) (32733 / 1000) (32743 / 1000)
    (50877 / 1000) (51011 / 1000) (-554607 / 1000) (15489 / 40000) (3023561 / 1000) (756711 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3707423 / 1000000) (13532247701 / 200000) (756711 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3707423 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3707423 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell541 :
    ∀ t ∈ Set.Icc ((42411 / 512000) : ℝ) (42419 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1180181179 / 1000000000) : ℝ) ≤ Real.exp (2 * (42411 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42411 / 512000)) (1180181179 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42419 / 512000) : ℝ)) ≤ (1180218061 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42419 / 512000)) (1180218061 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((33842394351 / 500000) : ℝ) ≤ Real.exp (3 * (3707539 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3707539 / 1000000)) (33842394351 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42411 / 512000) : ℝ) (42419 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3707539 / 1000000) (1853887 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42411 / 512000) (42419 / 512000) (1180181179 / 1000000000) (1180218061 / 1000000000) (3707539 / 1000000) (1853887 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42411 / 512000) (42419 / 512000) (3707539 / 1000000) (1853887 / 500000) (4092 / 125) (16373 / 500)
    (50891 / 1000) (2041 / 40) (-277313 / 500) (387127 / 1000000) (3023939 / 1000) (3782239 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3707539 / 1000000) (33842394351 / 500000) (3782239 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3707539 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3707539 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell542 :
    ∀ t ∈ Set.Icc ((42419 / 512000) : ℝ) (42427 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((59010903 / 50000000) : ℝ) ≤ Real.exp (2 * (42419 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42419 / 512000)) (59010903 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42427 / 512000) : ℝ)) ≤ (36882967 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42427 / 512000)) (36882967 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8463543387 / 125000) : ℝ) ≤ Real.exp (3 * (741531 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (741531 / 200000)) (8463543387 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42419 / 512000) : ℝ) (42427 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (741531 / 200000) (3707889 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42419 / 512000) (42427 / 512000) (59010903 / 50000000) (36882967 / 31250000) (741531 / 200000) (3707889 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42419 / 512000) (42427 / 512000) (741531 / 200000) (3707889 / 1000000) (32739 / 1000) (8187 / 250)
    (10181 / 200) (51039 / 1000) (-11093 / 20) (96757 / 250000) (604863 / 200) (3780923 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (741531 / 200000) (8463543387 / 125000) (3780923 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (741531 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (741531 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell543 :
    ∀ t ∈ Set.Icc ((42427 / 512000) : ℝ) (8487 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1180254943 / 1000000000) : ℝ) ≤ Real.exp (2 * (42427 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42427 / 512000)) (1180254943 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8487 / 102400) : ℝ)) ≤ (1180291827 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8487 / 102400)) (1180291827 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((33865855247 / 500000) : ℝ) ≤ Real.exp (3 * (370777 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (370777 / 100000)) (33865855247 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42427 / 512000) : ℝ) (8487 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (370777 / 100000) (741601 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42427 / 512000) (8487 / 102400) (1180254943 / 1000000000) (1180291827 / 1000000000) (370777 / 100000) (741601 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42427 / 512000) (8487 / 102400) (370777 / 100000) (741601 / 200000) (16371 / 500) (32751 / 1000)
    (50919 / 1000) (25527 / 500) (-277333 / 500) (386931 / 1000000) (3024693 / 1000) (3779619 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (370777 / 100000) (33865855247 / 500000) (3779619 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (370777 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (370777 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell544 :
    ∀ t ∈ Set.Icc ((8487 / 102400) : ℝ) (42443 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((590145913 / 500000000) : ℝ) ≤ Real.exp (2 * (8487 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8487 / 102400)) (590145913 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42443 / 512000) : ℝ)) ≤ (147541089 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42443 / 512000)) (147541089 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3387764261 / 50000) : ℝ) ≤ Real.exp (3 * (1853943 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1853943 / 500000)) (3387764261 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8487 / 102400) : ℝ) (42443 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1853943 / 500000) (3708121 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8487 / 102400) (42443 / 512000) (590145913 / 500000000) (147541089 / 125000000) (1853943 / 500000) (3708121 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8487 / 102400) (42443 / 512000) (1853943 / 500000) (3708121 / 1000000) (4093 / 125) (16377 / 500)
    (50933 / 1000) (12767 / 250) (-110937 / 200) (24177 / 62500) (3025071 / 1000) (14759 / 3906250)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1853943 / 500000) (3387764261 / 50000) (14759 / 3906250)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1853943 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1853943 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell545 :
    ∀ t ∈ Set.Icc ((42443 / 512000) : ℝ) (42451 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1180328711 / 1000000000) : ℝ) ≤ Real.exp (2 * (42443 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42443 / 512000)) (1180328711 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42451 / 512000) : ℝ)) ≤ (590182799 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42451 / 512000)) (590182799 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((67778868151 / 1000000) : ℝ) ≤ Real.exp (3 * (1854001 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1854001 / 500000)) (67778868151 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42443 / 512000) : ℝ) (42451 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1854001 / 500000) (3708237 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42443 / 512000) (42451 / 512000) (1180328711 / 1000000000) (590182799 / 500000000) (1854001 / 500000) (3708237 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42443 / 512000) (42451 / 512000) (1854001 / 500000) (3708237 / 1000000) (32747 / 1000) (32757 / 1000)
    (12737 / 250) (25541 / 500) (-110941 / 200) (193367 / 500000) (60509 / 20) (3776989 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1854001 / 500000) (67778868151 / 1000000) (3776989 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1854001 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1854001 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell546 :
    ∀ t ∈ Set.Icc ((42451 / 512000) : ℝ) (42459 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1180365597 / 1000000000) : ℝ) ≤ Real.exp (2 * (42451 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42451 / 512000)) (1180365597 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42459 / 512000) : ℝ)) ≤ (236080497 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42459 / 512000)) (236080497 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6780245929 / 100000) : ℝ) ≤ Real.exp (3 * (1854059 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1854059 / 500000)) (6780245929 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42451 / 512000) : ℝ) (42459 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1854059 / 500000) (3708353 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42451 / 512000) (42459 / 512000) (1180365597 / 1000000000) (236080497 / 200000000) (1854059 / 500000) (3708353 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42451 / 512000) (42459 / 512000) (1854059 / 500000) (3708353 / 1000000) (131 / 4) (32759 / 1000)
    (25481 / 500) (6387 / 125) (-22189 / 40) (96659 / 250000) (3025829 / 1000) (151027 / 40000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1854059 / 500000) (6780245929 / 100000) (151027 / 40000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1854059 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1854059 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell547 :
    ∀ t ∈ Set.Icc ((42459 / 512000) : ℝ) (42467 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((295100621 / 250000000) : ℝ) ≤ Real.exp (2 * (42459 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42459 / 512000)) (295100621 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42467 / 512000) : ℝ)) ≤ (1180439373 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42467 / 512000)) (1180439373 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((847825733 / 12500) : ℝ) ≤ Real.exp (3 * (1854117 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1854117 / 500000)) (847825733 / 12500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42459 / 512000) : ℝ) (42467 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1854117 / 500000) (3708469 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42459 / 512000) (42467 / 512000) (295100621 / 250000000) (1180439373 / 1000000000) (1854117 / 500000) (3708469 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42459 / 512000) (42467 / 512000) (1854117 / 500000) (3708469 / 1000000) (32753 / 1000) (16381 / 500)
    (6372 / 125) (51111 / 1000) (-69343 / 125) (193269 / 500000) (3026207 / 1000) (3774361 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1854117 / 500000) (847825733 / 12500) (3774361 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1854117 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1854117 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell548 :
    ∀ t ∈ Set.Icc ((42467 / 512000) : ℝ) (1699 / 20480), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((295109843 / 250000000) : ℝ) ≤ Real.exp (2 * (42467 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42467 / 512000)) (295109843 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1699 / 20480) : ℝ)) ≤ (590238131 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1699 / 20480)) (590238131 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((13569933241 / 200000) : ℝ) ≤ Real.exp (3 * (74167 / 20000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (74167 / 20000)) (13569933241 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42467 / 512000) : ℝ) (1699 / 20480),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (74167 / 20000) (741717 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42467 / 512000) (1699 / 20480) (295109843 / 250000000) (590238131 / 500000000) (74167 / 20000) (741717 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42467 / 512000) (1699 / 20480) (74167 / 20000) (741717 / 200000) (6551 / 200) (6553 / 200)
    (5099 / 100) (409 / 8) (-138691 / 250) (386439 / 1000000) (1513293 / 500) (471631 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (74167 / 20000) (13569933241 / 200000) (471631 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (74167 / 20000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (74167 / 20000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell549 :
    ∀ t ∈ Set.Icc ((1699 / 20480) : ℝ) (42483 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1180476261 / 1000000000) : ℝ) ≤ Real.exp (2 * (1699 / 20480)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1699 / 20480)) (1180476261 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42483 / 512000) : ℝ)) ≤ (1180513153 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42483 / 512000)) (1180513153 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((33936640993 / 500000) : ℝ) ≤ Real.exp (3 * (1854233 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1854233 / 500000)) (33936640993 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1699 / 20480) : ℝ) (42483 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1854233 / 500000) (3708701 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1699 / 20480) (42483 / 512000) (1180476261 / 1000000000) (1180513153 / 1000000000) (1854233 / 500000) (3708701 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1699 / 20480) (42483 / 512000) (1854233 / 500000) (3708701 / 1000000) (16379 / 500) (4096 / 125)
    (10201 / 200) (51139 / 1000) (-69348 / 125) (386341 / 1000000) (605393 / 200) (754347 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1854233 / 500000) (33936640993 / 500000) (754347 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1854233 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1854233 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell550 :
    ∀ t ∈ Set.Icc ((42483 / 512000) : ℝ) (42491 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((9222759 / 7812500) : ℝ) ≤ Real.exp (2 * (42483 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42483 / 512000)) (9222759 / 7812500) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42491 / 512000) : ℝ)) ≤ (295137511 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42491 / 512000)) (295137511 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((67896905987 / 1000000) : ℝ) ≤ Real.exp (3 * (1854291 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1854291 / 500000)) (67896905987 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42483 / 512000) : ℝ) (42491 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1854291 / 500000) (3708817 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42483 / 512000) (42491 / 512000) (9222759 / 7812500) (295137511 / 250000000) (1854291 / 500000) (3708817 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42483 / 512000) (42491 / 512000) (1854291 / 500000) (3708817 / 1000000) (32761 / 1000) (3277 / 100)
    (51019 / 1000) (51153 / 1000) (-138701 / 250) (386243 / 1000000) (3027343 / 1000) (3770423 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1854291 / 500000) (67896905987 / 1000000) (3770423 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1854291 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1854291 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell551 :
    ∀ t ∈ Set.Icc ((42491 / 512000) : ℝ) (42499 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1180550043 / 1000000000) : ℝ) ≤ Real.exp (2 * (42491 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42491 / 512000)) (1180550043 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42499 / 512000) : ℝ)) ≤ (1180586937 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42499 / 512000)) (1180586937 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((67920334449 / 1000000) : ℝ) ≤ Real.exp (3 * (3708697 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3708697 / 1000000)) (67920334449 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42491 / 512000) : ℝ) (42499 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3708697 / 1000000) (927233 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42491 / 512000) (42499 / 512000) (1180550043 / 1000000000) (1180586937 / 1000000000) (3708697 / 1000000) (927233 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42491 / 512000) (42499 / 512000) (3708697 / 1000000) (927233 / 250000) (8191 / 250) (32773 / 1000)
    (51033 / 1000) (51167 / 1000) (-554823 / 1000) (193073 / 500000) (3027719 / 1000) (1884561 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3708697 / 1000000) (67920334449 / 1000000) (1884561 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3708697 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3708697 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell552 :
    ∀ t ∈ Set.Icc ((42499 / 512000) : ℝ) (42507 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((147573367 / 125000000) : ℝ) ≤ Real.exp (2 * (42499 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42499 / 512000)) (147573367 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42507 / 512000) : ℝ)) ≤ (1180623831 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42507 / 512000)) (1180623831 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((67943974827 / 1000000) : ℝ) ≤ Real.exp (3 * (3708813 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3708813 / 1000000)) (67943974827 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42499 / 512000) : ℝ) (42507 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3708813 / 1000000) (463631 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42499 / 512000) (42507 / 512000) (147573367 / 125000000) (1180623831 / 1000000000) (3708813 / 1000000) (463631 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42499 / 512000) (42507 / 512000) (3708813 / 1000000) (463631 / 125000) (16383 / 500) (4097 / 125)
    (51047 / 1000) (51181 / 1000) (-554843 / 1000) (386047 / 1000000) (1514049 / 500) (3767811 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3708813 / 1000000) (67943974827 / 1000000) (3767811 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3708813 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3708813 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell553 :
    ∀ t ∈ Set.Icc ((42507 / 512000) : ℝ) (8503 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((118062383 / 100000000) : ℝ) ≤ Real.exp (2 * (42507 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42507 / 512000)) (118062383 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8503 / 102400) : ℝ)) ≤ (590330363 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8503 / 102400)) (590330363 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((67967623433 / 1000000) : ℝ) ≤ Real.exp (3 * (3708929 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3708929 / 1000000)) (67967623433 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42507 / 512000) : ℝ) (8503 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3708929 / 1000000) (927291 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42507 / 512000) (8503 / 102400) (118062383 / 100000000) (590330363 / 500000000) (3708929 / 1000000) (927291 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42507 / 512000) (8503 / 102400) (3708929 / 1000000) (927291 / 250000) (32769 / 1000) (32779 / 1000)
    (51061 / 1000) (12799 / 250) (-277431 / 500) (385949 / 1000000) (757119 / 250) (7533 / 2000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3708929 / 1000000) (67967623433 / 1000000) (7533 / 2000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3708929 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3708929 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell554 :
    ∀ t ∈ Set.Icc ((8503 / 102400) : ℝ) (42523 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((47226429 / 40000000) : ℝ) ≤ Real.exp (2 * (8503 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8503 / 102400)) (47226429 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42523 / 512000) : ℝ)) ≤ (590348811 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42523 / 512000)) (590348811 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((67991280271 / 1000000) : ℝ) ≤ Real.exp (3 * (741809 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (741809 / 200000)) (67991280271 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8503 / 102400) : ℝ) (42523 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (741809 / 200000) (23183 / 6250) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8503 / 102400) (42523 / 512000) (47226429 / 40000000) (590348811 / 500000000) (741809 / 200000) (23183 / 6250) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8503 / 102400) (42523 / 512000) (741809 / 200000) (23183 / 6250) (8193 / 250) (32781 / 1000)
    (12769 / 250) (5121 / 100) (-277441 / 500) (385851 / 1000000) (605771 / 200) (3765189 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (741809 / 200000) (67991280271 / 1000000) (3765189 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (741809 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (741809 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell555 :
    ∀ t ∈ Set.Icc ((42523 / 512000) : ℝ) (42531 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1180697621 / 1000000000) : ℝ) ≤ Real.exp (2 * (42523 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42523 / 512000)) (1180697621 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42531 / 512000) : ℝ)) ≤ (29518363 / 25000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42531 / 512000)) (29518363 / 25000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((34007472671 / 500000) : ℝ) ≤ Real.exp (3 * (3709161 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3709161 / 1000000)) (34007472671 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42523 / 512000) : ℝ) (42531 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3709161 / 1000000) (927349 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42523 / 512000) (42531 / 512000) (1180697621 / 1000000000) (29518363 / 25000000) (3709161 / 1000000) (927349 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42523 / 512000) (42531 / 512000) (3709161 / 1000000) (927349 / 250000) (1311 / 40) (4098 / 125)
    (5109 / 100) (6403 / 125) (-277451 / 500) (385753 / 1000000) (1514617 / 500) (3763879 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3709161 / 1000000) (34007472671 / 500000) (3763879 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3709161 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3709161 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell556 :
    ∀ t ∈ Set.Icc ((42531 / 512000) : ℝ) (42539 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1180734519 / 1000000000) : ℝ) ≤ Real.exp (2 * (42531 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42531 / 512000)) (1180734519 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42539 / 512000) : ℝ)) ≤ (590385709 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42539 / 512000)) (590385709 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1360772373 / 20000) : ℝ) ≤ Real.exp (3 * (3709277 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3709277 / 1000000)) (1360772373 / 20000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42531 / 512000) : ℝ) (42539 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3709277 / 1000000) (463689 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42531 / 512000) (42539 / 512000) (1180734519 / 1000000000) (590385709 / 500000000) (3709277 / 1000000) (463689 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42531 / 512000) (42539 / 512000) (3709277 / 1000000) (463689 / 125000) (32777 / 1000) (32787 / 1000)
    (6388 / 125) (25619 / 500) (-554921 / 1000) (77131 / 200000) (3029613 / 1000) (376257 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3709277 / 1000000) (1360772373 / 20000) (376257 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3709277 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3709277 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell557 :
    ∀ t ∈ Set.Icc ((42539 / 512000) : ℝ) (42547 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1180771417 / 1000000000) : ℝ) ≤ Real.exp (2 * (42539 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42539 / 512000)) (1180771417 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42547 / 512000) : ℝ)) ≤ (590404159 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42547 / 512000)) (590404159 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((34031150099 / 500000) : ℝ) ≤ Real.exp (3 * (3709393 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3709393 / 1000000)) (34031150099 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42539 / 512000) : ℝ) (42547 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3709393 / 1000000) (927407 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42539 / 512000) (42547 / 512000) (1180771417 / 1000000000) (590404159 / 500000000) (3709393 / 1000000) (927407 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42539 / 512000) (42547 / 512000) (3709393 / 1000000) (927407 / 250000) (1639 / 50) (3279 / 100)
    (25559 / 500) (51253 / 1000) (-554941 / 1000) (385557 / 1000000) (378749 / 125) (188063 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3709393 / 1000000) (34031150099 / 500000) (188063 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3709393 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3709393 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell558 :
    ∀ t ∈ Set.Icc ((42547 / 512000) : ℝ) (8511 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1180808317 / 1000000000) : ℝ) ≤ Real.exp (2 * (42547 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42547 / 512000)) (1180808317 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8511 / 102400) : ℝ)) ≤ (1180845219 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8511 / 102400)) (1180845219 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((68085989989 / 1000000) : ℝ) ≤ Real.exp (3 * (3709509 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3709509 / 1000000)) (68085989989 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42547 / 512000) : ℝ) (8511 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3709509 / 1000000) (231859 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42547 / 512000) (8511 / 102400) (1180808317 / 1000000000) (1180845219 / 1000000000) (3709509 / 1000000) (231859 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42547 / 512000) (8511 / 102400) (3709509 / 1000000) (231859 / 62500) (32783 / 1000) (4099 / 125)
    (12783 / 250) (51267 / 1000) (-554961 / 1000) (385459 / 1000000) (3030371 / 1000) (234997 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3709509 / 1000000) (68085989989 / 1000000) (234997 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3709509 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3709509 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell559 :
    ∀ t ∈ Set.Icc ((8511 / 102400) : ℝ) (42563 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((590422609 / 500000000) : ℝ) ≤ Real.exp (2 * (8511 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8511 / 102400)) (590422609 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42563 / 512000) : ℝ)) ≤ (1180882121 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42563 / 512000)) (1180882121 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2724387521 / 40000) : ℝ) ≤ Real.exp (3 * (29677 / 8000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (29677 / 8000)) (2724387521 / 40000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8511 / 102400) : ℝ) (42563 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (29677 / 8000) (185493 / 50000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8511 / 102400) (42563 / 512000) (590422609 / 500000000) (1180882121 / 1000000000) (29677 / 8000) (185493 / 50000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8511 / 102400) (42563 / 512000) (29677 / 8000) (185493 / 50000) (16393 / 500) (6559 / 200)
    (51147 / 1000) (51281 / 1000) (-27749 / 50) (385361 / 1000000) (12123 / 4) (3758643 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (29677 / 8000) (2724387521 / 40000) (3758643 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (29677 / 8000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (29677 / 8000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch027 :
    ∀ t ∈ Set.Icc ((42403 / 512000) : ℝ) (42563 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell540
      hpThetaDensityLowerExpCompact_cell541)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell542
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell543
      hpThetaDensityLowerExpCompact_cell544)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell545
      hpThetaDensityLowerExpCompact_cell546)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell547
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell548
      hpThetaDensityLowerExpCompact_cell549))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell550
      hpThetaDensityLowerExpCompact_cell551)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell552
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell553
      hpThetaDensityLowerExpCompact_cell554)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell555
      hpThetaDensityLowerExpCompact_cell556)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell557
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell558
      hpThetaDensityLowerExpCompact_cell559)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch027
end HodgeProofHP
