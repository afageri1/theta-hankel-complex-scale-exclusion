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
theorem hpThetaDensityLowerExpCompact_cell780 :
    ∀ t ∈ Set.Icc ((45027 / 512000) : ℝ) (45043 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((238460597 / 200000000) : ℝ) ≤ Real.exp (2 * (45027 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45027 / 512000)) (238460597 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45043 / 512000) : ℝ)) ≤ (1192377507 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45043 / 512000)) (1192377507 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((948450927 / 12500) : ℝ) ≤ Real.exp (3 * (3745619 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3745619 / 1000000)) (948450927 / 12500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45027 / 512000) : ℝ) (45043 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3745619 / 1000000) (1872987 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45027 / 512000) (45043 / 512000) (238460597 / 200000000) (1192377507 / 1000000000) (3745619 / 1000000) (1872987 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45027 / 512000) (45043 / 512000) (3745619 / 1000000) (1872987 / 500000) (16821 / 500) (4207 / 125)
    (13903 / 250) (27909 / 500) (-112041 / 200) (178059 / 500000) (3150497 / 1000) (3373923 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3745619 / 1000000) (948450927 / 12500) (3373923 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3745619 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3745619 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell781 :
    ∀ t ∈ Set.Icc ((45043 / 512000) : ℝ) (45059 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((596188753 / 500000000) : ℝ) ≤ Real.exp (2 * (45043 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45043 / 512000)) (596188753 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45059 / 512000) : ℝ)) ≤ (1192452033 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45059 / 512000)) (1192452033 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((75929357833 / 1000000) : ℝ) ≤ Real.exp (3 * (3745853 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3745853 / 1000000)) (75929357833 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45043 / 512000) : ℝ) (45059 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3745853 / 1000000) (117069 / 31250) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45043 / 512000) (45059 / 512000) (596188753 / 500000000) (1192452033 / 1000000000) (3745853 / 1000000) (117069 / 31250) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45043 / 512000) (45059 / 512000) (3745853 / 1000000) (117069 / 31250) (4206 / 125) (16831 / 500)
    (27821 / 500) (6981 / 125) (-14006 / 25) (71187 / 200000) (787821 / 250) (674311 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3745853 / 1000000) (75929357833 / 1000000) (674311 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3745853 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3745853 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell782 :
    ∀ t ∈ Set.Icc ((45059 / 512000) : ℝ) (1803 / 20480), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((18632063 / 15625000) : ℝ) ≤ Real.exp (2 * (45059 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45059 / 512000)) (18632063 / 15625000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1803 / 20480) : ℝ)) ≤ (298131641 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1803 / 20480)) (298131641 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((9497863359 / 125000) : ℝ) ≤ Real.exp (3 * (468261 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (468261 / 125000)) (9497863359 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45059 / 512000) : ℝ) (1803 / 20480),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (468261 / 125000) (1873221 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45059 / 512000) (1803 / 20480) (18632063 / 15625000) (298131641 / 250000000) (468261 / 125000) (1873221 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45059 / 512000) (1803 / 20480) (468261 / 125000) (1873221 / 500000) (16827 / 500) (33667 / 1000)
    (6959 / 125) (55877 / 1000) (-14007 / 25) (1423 / 4000) (394009 / 125) (3369179 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (468261 / 125000) (9497863359 / 125000) (3369179 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (468261 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (468261 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell783 :
    ∀ t ∈ Set.Icc ((1803 / 20480) : ℝ) (45091 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1192526563 / 1000000000) : ℝ) ≤ Real.exp (2 * (1803 / 20480)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1803 / 20480)) (1192526563 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45091 / 512000) : ℝ)) ≤ (1192601099 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45091 / 512000)) (1192601099 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((76036265567 / 1000000) : ℝ) ≤ Real.exp (3 * (1873161 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1873161 / 500000)) (76036265567 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1803 / 20480) : ℝ) (45091 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1873161 / 500000) (936669 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1803 / 20480) (45091 / 512000) (1192526563 / 1000000000) (1192601099 / 1000000000) (1873161 / 500000) (936669 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1803 / 20480) (45091 / 512000) (1873161 / 500000) (936669 / 250000) (33659 / 1000) (33673 / 1000)
    (27851 / 500) (55907 / 1000) (-112063 / 200) (355567 / 1000000) (3152859 / 1000) (673363 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1873161 / 500000) (76036265567 / 1000000) (673363 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1873161 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1873161 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell784 :
    ∀ t ∈ Set.Icc ((45091 / 512000) : ℝ) (45107 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((596300549 / 500000000) : ℝ) ≤ Real.exp (2 * (45091 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45091 / 512000)) (596300549 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45107 / 512000) : ℝ)) ≤ (1192675639 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45107 / 512000)) (1192675639 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((38044830867 / 500000) : ℝ) ≤ Real.exp (3 * (936639 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (936639 / 250000)) (38044830867 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45091 / 512000) : ℝ) (45107 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (936639 / 250000) (374691 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45091 / 512000) (45107 / 512000) (596300549 / 500000000) (1192675639 / 1000000000) (936639 / 250000) (374691 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45091 / 512000) (45107 / 512000) (936639 / 250000) (374691 / 100000) (6733 / 200) (33679 / 1000)
    (13933 / 250) (55937 / 1000) (-560351 / 1000) (44423 / 125000) (3153647 / 1000) (841113 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (936639 / 250000) (38044830867 / 500000) (841113 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (936639 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (936639 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell785 :
    ∀ t ∈ Set.Icc ((45107 / 512000) : ℝ) (45123 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((596337819 / 500000000) : ℝ) ≤ Real.exp (2 * (45107 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45107 / 512000)) (596337819 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45123 / 512000) : ℝ)) ≤ (1192750183 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45123 / 512000)) (1192750183 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((76143095397 / 1000000) : ℝ) ≤ Real.exp (3 * (374679 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (374679 / 100000)) (76143095397 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45107 / 512000) : ℝ) (45123 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (374679 / 100000) (468393 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45107 / 512000) (45123 / 512000) (596337819 / 500000000) (1192750183 / 1000000000) (374679 / 100000) (468393 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45107 / 512000) (45123 / 512000) (374679 / 100000) (468393 / 125000) (3367 / 100) (8421 / 250)
    (55761 / 1000) (27983 / 500) (-280193 / 500) (177601 / 500000) (630887 / 200) (3362091 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (374679 / 100000) (76143095397 / 1000000) (3362091 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (374679 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (374679 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell786 :
    ∀ t ∈ Set.Icc ((45123 / 512000) : ℝ) (45139 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((596375091 / 500000000) : ℝ) ≤ Real.exp (2 * (45123 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45123 / 512000)) (596375091 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45139 / 512000) : ℝ)) ≤ (1192824733 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45139 / 512000)) (1192824733 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((9524570823 / 125000) : ℝ) ≤ Real.exp (3 * (234189 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (234189 / 62500)) (9524570823 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45123 / 512000) : ℝ) (45139 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (234189 / 62500) (3747379 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45123 / 512000) (45139 / 512000) (596375091 / 500000000) (1192824733 / 1000000000) (234189 / 62500) (3747379 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45123 / 512000) (45139 / 512000) (234189 / 62500) (3747379 / 1000000) (8419 / 250) (3369 / 100)
    (55791 / 1000) (55997 / 1000) (-70052 / 125) (355019 / 1000000) (1577613 / 500) (839933 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (234189 / 62500) (9524570823 / 125000) (839933 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (234189 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (234189 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell787 :
    ∀ t ∈ Set.Icc ((45139 / 512000) : ℝ) (9031 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((298206183 / 250000000) : ℝ) ≤ Real.exp (2 * (45139 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45139 / 512000)) (298206183 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9031 / 102400) : ℝ)) ≤ (596449643 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9031 / 102400)) (596449643 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((76250075321 / 1000000) : ℝ) ≤ Real.exp (3 * (1873629 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1873629 / 500000)) (76250075321 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45139 / 512000) : ℝ) (9031 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1873629 / 500000) (3747613 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45139 / 512000) (9031 / 102400) (298206183 / 250000000) (596449643 / 500000000) (1873629 / 500000) (3747613 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45139 / 512000) (9031 / 102400) (1873629 / 500000) (3747613 / 1000000) (16841 / 500) (6739 / 200)
    (55821 / 1000) (28013 / 500) (-140113 / 250) (88709 / 250000) (631203 / 200) (1678687 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1873629 / 500000) (76250075321 / 1000000) (1678687 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1873629 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1873629 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell788 :
    ∀ t ∈ Set.Icc ((9031 / 102400) : ℝ) (45171 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((238579857 / 200000000) : ℝ) ≤ Real.exp (2 * (9031 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9031 / 102400)) (238579857 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45171 / 512000) : ℝ)) ≤ (238594769 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45171 / 512000)) (238594769 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((38151925273 / 500000) : ℝ) ≤ Real.exp (3 * (3747493 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3747493 / 1000000)) (38151925273 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9031 / 102400) : ℝ) (45171 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3747493 / 1000000) (3747847 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (9031 / 102400) (45171 / 512000) (238579857 / 200000000) (238594769 / 200000000) (3747493 / 1000000) (3747847 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (9031 / 102400) (45171 / 512000) (3747493 / 1000000) (3747847 / 1000000) (33687 / 1000) (33701 / 1000)
    (55851 / 1000) (7007 / 125) (-140123 / 250) (354653 / 1000000) (3156803 / 1000) (26211 / 7812500)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3747493 / 1000000) (38151925273 / 500000) (26211 / 7812500)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3747493 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3747493 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell789 :
    ∀ t ∈ Set.Icc ((45171 / 512000) : ℝ) (45187 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((298243461 / 250000000) : ℝ) ≤ Real.exp (2 * (45171 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45171 / 512000)) (298243461 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45187 / 512000) : ℝ)) ≤ (149131051 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45187 / 512000)) (149131051 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((38178717311 / 500000) : ℝ) ≤ Real.exp (3 * (3747727 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3747727 / 1000000)) (38178717311 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45171 / 512000) : ℝ) (45187 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3747727 / 1000000) (3748081 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45171 / 512000) (45187 / 512000) (298243461 / 250000000) (149131051 / 125000000) (3747727 / 1000000) (3748081 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45171 / 512000) (45187 / 512000) (3747727 / 1000000) (3748081 / 1000000) (33693 / 1000) (33707 / 1000)
    (1397 / 25) (28043 / 500) (-560527 / 1000) (35447 / 100000) (3157591 / 1000) (1676327 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3747727 / 1000000) (38178717311 / 500000) (1676327 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3747727 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3747727 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell790 :
    ∀ t ∈ Set.Icc ((45187 / 512000) : ℝ) (45203 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1193048407 / 1000000000) : ℝ) ≤ Real.exp (2 * (45187 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45187 / 512000)) (1193048407 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45203 / 512000) : ℝ)) ≤ (37285093 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45203 / 512000)) (37285093 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((9551382041 / 125000) : ℝ) ≤ Real.exp (3 * (3747961 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3747961 / 1000000)) (9551382041 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45187 / 512000) : ℝ) (45203 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3747961 / 1000000) (937079 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45187 / 512000) (45203 / 512000) (1193048407 / 1000000000) (37285093 / 31250000) (3747961 / 1000000) (937079 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45187 / 512000) (45203 / 512000) (3747961 / 1000000) (937079 / 250000) (16849 / 500) (4214 / 125)
    (5591 / 100) (14029 / 250) (-560557 / 1000) (22143 / 62500) (3158383 / 1000) (3350301 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3747961 / 1000000) (9551382041 / 125000) (3350301 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3747961 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3747961 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell791 :
    ∀ t ∈ Set.Icc ((45203 / 512000) : ℝ) (45219 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((47724919 / 40000000) : ℝ) ≤ Real.exp (2 * (45203 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45203 / 512000)) (47724919 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45219 / 512000) : ℝ)) ≤ (1193197549 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45219 / 512000)) (1193197549 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((7646471569 / 100000) : ℝ) ≤ Real.exp (3 * (749639 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (749639 / 200000)) (7646471569 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45203 / 512000) : ℝ) (45219 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (749639 / 200000) (74971 / 20000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45203 / 512000) (45219 / 512000) (47724919 / 40000000) (1193197549 / 1000000000) (749639 / 200000) (74971 / 20000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45203 / 512000) (45219 / 512000) (749639 / 200000) (74971 / 20000) (4213 / 125) (16859 / 500)
    (2797 / 50) (28073 / 500) (-70074 / 125) (177053 / 500000) (789793 / 250) (66959 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (749639 / 200000) (7646471569 / 100000) (66959 / 20000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (749639 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (749639 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell792 :
    ∀ t ∈ Set.Icc ((45219 / 512000) : ℝ) (9047 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((298299387 / 250000000) : ℝ) ≤ Real.exp (2 * (45219 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45219 / 512000)) (298299387 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9047 / 102400) : ℝ)) ≤ (596636063 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9047 / 102400)) (596636063 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((76518642289 / 1000000) : ℝ) ≤ Real.exp (3 * (374843 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (374843 / 100000)) (76518642289 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45219 / 512000) : ℝ) (9047 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (374843 / 100000) (234299 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45219 / 512000) (9047 / 102400) (298299387 / 250000000) (596636063 / 500000000) (374843 / 100000) (234299 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45219 / 512000) (9047 / 102400) (374843 / 100000) (234299 / 62500) (3371 / 100) (33723 / 1000)
    (5597 / 100) (2247 / 40) (-70079 / 125) (353923 / 1000000) (3159961 / 1000) (334559 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (374843 / 100000) (76518642289 / 1000000) (334559 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (374843 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (374843 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell793 :
    ∀ t ∈ Set.Icc ((9047 / 102400) : ℝ) (45251 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((9546177 / 8000000) : ℝ) ≤ Real.exp (2 * (9047 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9047 / 102400)) (9546177 / 8000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45251 / 512000) : ℝ)) ≤ (298336677 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45251 / 512000)) (298336677 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((38286188601 / 500000) : ℝ) ≤ Real.exp (3 * (468583 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (468583 / 125000)) (38286188601 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9047 / 102400) : ℝ) (45251 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (468583 / 125000) (3749019 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (9047 / 102400) (45251 / 512000) (9546177 / 8000000) (298336677 / 250000000) (468583 / 125000) (3749019 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (9047 / 102400) (45251 / 512000) (468583 / 125000) (3749019 / 1000000) (6743 / 200) (33729 / 1000)
    (55999 / 1000) (11241 / 200) (-280331 / 500) (353741 / 1000000) (3160753 / 1000) (3343243 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (468583 / 125000) (38286188601 / 500000) (3343243 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (468583 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (468583 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell794 :
    ∀ t ∈ Set.Icc ((45251 / 512000) : ℝ) (45267 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1193346707 / 1000000000) : ℝ) ≤ Real.exp (2 * (45251 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45251 / 512000)) (1193346707 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45267 / 512000) : ℝ)) ≤ (596710647 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45267 / 512000)) (596710647 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1532522997 / 20000) : ℝ) ≤ Real.exp (3 * (1874449 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1874449 / 500000)) (1532522997 / 20000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45251 / 512000) : ℝ) (45267 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1874449 / 500000) (3749253 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45251 / 512000) (45267 / 512000) (1193346707 / 1000000000) (596710647 / 500000000) (1874449 / 500000) (3749253 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45251 / 512000) (45267 / 512000) (1874449 / 500000) (3749253 / 1000000) (33721 / 1000) (6747 / 200)
    (56029 / 1000) (11247 / 200) (-560697 / 1000) (353559 / 1000000) (3161543 / 1000) (3340897 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1874449 / 500000) (1532522997 / 20000) (3340897 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1874449 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1874449 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell795 :
    ∀ t ∈ Set.Icc ((45267 / 512000) : ℝ) (45283 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1193421293 / 1000000000) : ℝ) ≤ Real.exp (2 * (45267 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45267 / 512000)) (1193421293 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45283 / 512000) : ℝ)) ≤ (238699177 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45283 / 512000)) (238699177 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3833998013 / 50000) : ℝ) ≤ Real.exp (3 * (937283 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (937283 / 250000)) (3833998013 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45267 / 512000) : ℝ) (45283 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (937283 / 250000) (3749487 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45267 / 512000) (45283 / 512000) (1193421293 / 1000000000) (238699177 / 200000000) (937283 / 250000) (3749487 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45267 / 512000) (45283 / 512000) (937283 / 250000) (3749487 / 1000000) (33727 / 1000) (1687 / 50)
    (56059 / 1000) (11253 / 200) (-140183 / 250) (353377 / 1000000) (790583 / 250) (417319 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (937283 / 250000) (3833998013 / 50000) (417319 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (937283 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (937283 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell796 :
    ∀ t ∈ Set.Icc ((45283 / 512000) : ℝ) (45299 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((298373971 / 250000000) : ℝ) ≤ Real.exp (2 * (45283 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45283 / 512000)) (298373971 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45299 / 512000) : ℝ)) ≤ (1193570481 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45299 / 512000)) (1193570481 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((76734038659 / 1000000) : ℝ) ≤ Real.exp (3 * (3749367 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3749367 / 1000000)) (76734038659 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45283 / 512000) : ℝ) (45299 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3749367 / 1000000) (1874861 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45283 / 512000) (45299 / 512000) (298373971 / 250000000) (1193570481 / 1000000000) (3749367 / 1000000) (1874861 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45283 / 512000) (45299 / 512000) (3749367 / 1000000) (1874861 / 500000) (8433 / 250) (16873 / 500)
    (56089 / 1000) (11259 / 200) (-70096 / 125) (176597 / 500000) (25305 / 8) (3336199 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3749367 / 1000000) (76734038659 / 1000000) (3336199 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3749367 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3749367 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell797 :
    ∀ t ∈ Set.Icc ((45299 / 512000) : ℝ) (9063 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((14919631 / 12500000) : ℝ) ≤ Real.exp (2 * (45299 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45299 / 512000)) (14919631 / 12500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9063 / 102400) : ℝ)) ≤ (596822541 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9063 / 102400)) (596822541 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((76787924833 / 1000000) : ℝ) ≤ Real.exp (3 * (3749601 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3749601 / 1000000)) (76787924833 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45299 / 512000) : ℝ) (9063 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3749601 / 1000000) (937489 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45299 / 512000) (9063 / 102400) (14919631 / 12500000) (596822541 / 500000000) (3749601 / 1000000) (937489 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45299 / 512000) (9063 / 102400) (3749601 / 1000000) (937489 / 250000) (16869 / 500) (4219 / 125)
    (56119 / 1000) (2253 / 40) (-280401 / 500) (88253 / 250000) (632783 / 200) (1666929 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3749601 / 1000000) (76787924833 / 1000000) (1666929 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3749601 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3749601 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell798 :
    ∀ t ∈ Set.Icc ((9063 / 102400) : ℝ) (45331 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1193645081 / 1000000000) : ℝ) ≤ Real.exp (2 * (9063 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9063 / 102400)) (1193645081 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45331 / 512000) : ℝ)) ≤ (1193719687 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45331 / 512000)) (1193719687 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((122947327 / 1600) : ℝ) ≤ Real.exp (3 * (937459 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (937459 / 250000)) (122947327 / 1600) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9063 / 102400) : ℝ) (45331 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (937459 / 250000) (375019 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (9063 / 102400) (45331 / 512000) (1193645081 / 1000000000) (1193719687 / 1000000000) (937459 / 250000) (375019 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (9063 / 102400) (45331 / 512000) (937459 / 250000) (375019 / 100000) (33743 / 1000) (33757 / 1000)
    (56149 / 1000) (28177 / 500) (-280421 / 500) (35283 / 100000) (395588 / 125) (832877 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (937459 / 250000) (122947327 / 1600) (832877 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (937459 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (937459 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell799 :
    ∀ t ∈ Set.Icc ((45331 / 512000) : ℝ) (45347 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((596859843 / 500000000) : ℝ) ≤ Real.exp (2 * (45331 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45331 / 512000)) (596859843 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45347 / 512000) : ℝ)) ≤ (1193794297 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45347 / 512000)) (1193794297 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3844802071 / 50000) : ℝ) ≤ Real.exp (3 * (375007 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (375007 / 100000)) (3844802071 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45331 / 512000) : ℝ) (45347 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (375007 / 100000) (150017 / 40000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45331 / 512000) (45347 / 512000) (596859843 / 500000000) (1193794297 / 1000000000) (375007 / 100000) (150017 / 40000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45331 / 512000) (45347 / 512000) (375007 / 100000) (150017 / 40000) (33749 / 1000) (33763 / 1000)
    (56179 / 1000) (11277 / 200) (-70109 / 125) (44081 / 125000) (1582749 / 500) (3329171 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (375007 / 100000) (3844802071 / 50000) (3329171 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (375007 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (375007 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch039 :
    ∀ t ∈ Set.Icc ((45027 / 512000) : ℝ) (45347 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell780
      hpThetaDensityLowerExpCompact_cell781)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell782
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell783
      hpThetaDensityLowerExpCompact_cell784)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell785
      hpThetaDensityLowerExpCompact_cell786)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell787
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell788
      hpThetaDensityLowerExpCompact_cell789))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell790
      hpThetaDensityLowerExpCompact_cell791)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell792
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell793
      hpThetaDensityLowerExpCompact_cell794)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell795
      hpThetaDensityLowerExpCompact_cell796)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell797
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell798
      hpThetaDensityLowerExpCompact_cell799)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch039
end HodgeProofHP
