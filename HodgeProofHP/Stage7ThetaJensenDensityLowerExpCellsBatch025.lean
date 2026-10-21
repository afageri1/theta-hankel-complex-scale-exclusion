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
theorem hpThetaDensityLowerExpCompact_cell500 :
    ∀ t ∈ Set.Icc ((42139 / 512000) : ℝ) (42143 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1178927903 / 1000000000) : ℝ) ≤ Real.exp (2 * (42139 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42139 / 512000)) (1178927903 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42143 / 512000) : ℝ)) ≤ (294736581 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42143 / 512000)) (294736581 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((13378013303 / 200000) : ℝ) ≤ Real.exp (3 * (1851801 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1851801 / 500000)) (13378013303 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42139 / 512000) : ℝ) (42143 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1851801 / 500000) (1851889 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42139 / 512000) (42143 / 512000) (1178927903 / 1000000000) (294736581 / 250000000) (1851801 / 500000) (1851889 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42139 / 512000) (42143 / 512000) (1851801 / 500000) (1851889 / 500000) (8161 / 250) (32651 / 1000)
    (50423 / 1000) (12631 / 250) (-69277 / 125) (390461 / 1000000) (752731 / 250) (478397 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1851801 / 500000) (13378013303 / 200000) (478397 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1851801 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1851801 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell501 :
    ∀ t ∈ Set.Icc ((42143 / 512000) : ℝ) (42147 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1178946323 / 1000000000) : ℝ) ≤ Real.exp (2 * (42143 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42143 / 512000)) (1178946323 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42147 / 512000) : ℝ)) ≤ (589482373 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42147 / 512000)) (589482373 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66901505689 / 1000000) : ℝ) ≤ Real.exp (3 * (3703659 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3703659 / 1000000)) (66901505689 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42143 / 512000) : ℝ) (42147 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3703659 / 1000000) (925959 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42143 / 512000) (42147 / 512000) (1178946323 / 1000000000) (589482373 / 500000000) (3703659 / 1000000) (925959 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42143 / 512000) (42147 / 512000) (3703659 / 1000000) (925959 / 250000) (6529 / 200) (8163 / 250)
    (5043 / 100) (50531 / 1000) (-277111 / 500) (97603 / 250000) (3011113 / 1000) (3826521 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3703659 / 1000000) (66901505689 / 1000000) (3826521 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3703659 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3703659 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell502 :
    ∀ t ∈ Set.Icc ((42147 / 512000) : ℝ) (42151 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((235792949 / 200000000) : ℝ) ≤ Real.exp (2 * (42147 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42147 / 512000)) (235792949 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42151 / 512000) : ℝ)) ≤ (1178983167 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42151 / 512000)) (1178983167 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66913147559 / 1000000) : ℝ) ≤ Real.exp (3 * (3703717 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3703717 / 1000000)) (66913147559 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42147 / 512000) : ℝ) (42151 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3703717 / 1000000) (1851947 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42147 / 512000) (42151 / 512000) (235792949 / 200000000) (1178983167 / 1000000000) (3703717 / 1000000) (1851947 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42147 / 512000) (42151 / 512000) (3703717 / 1000000) (1851947 / 500000) (16323 / 500) (16327 / 500)
    (50437 / 1000) (25269 / 500) (-69279 / 125) (390363 / 1000000) (1505651 / 500) (765171 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3703717 / 1000000) (66913147559 / 1000000) (765171 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3703717 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3703717 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell503 :
    ∀ t ∈ Set.Icc ((42151 / 512000) : ℝ) (8431 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((589491583 / 500000000) : ℝ) ≤ Real.exp (2 * (42151 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42151 / 512000)) (589491583 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8431 / 102400) : ℝ)) ≤ (1179001589 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8431 / 102400)) (1179001589 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((33462395727 / 500000) : ℝ) ≤ Real.exp (3 * (148151 / 40000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (148151 / 40000)) (33462395727 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42151 / 512000) : ℝ) (8431 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (148151 / 40000) (231497 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42151 / 512000) (8431 / 102400) (589491583 / 500000000) (1179001589 / 1000000000) (148151 / 40000) (231497 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42151 / 512000) (8431 / 102400) (148151 / 40000) (231497 / 62500) (4081 / 125) (6531 / 200)
    (12611 / 250) (10109 / 200) (-277121 / 500) (390313 / 1000000) (301149 / 100) (382519 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (148151 / 40000) (33462395727 / 500000) (382519 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (148151 / 40000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (148151 / 40000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell504 :
    ∀ t ∈ Set.Icc ((8431 / 102400) : ℝ) (42159 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((294750397 / 250000000) : ℝ) ≤ Real.exp (2 * (8431 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8431 / 102400)) (294750397 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42159 / 512000) : ℝ)) ≤ (1179020011 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42159 / 512000)) (1179020011 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((535491499 / 8000) : ℝ) ≤ Real.exp (3 * (3703833 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3703833 / 1000000)) (535491499 / 8000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8431 / 102400) : ℝ) (42159 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3703833 / 1000000) (370401 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8431 / 102400) (42159 / 512000) (294750397 / 250000000) (1179020011 / 1000000000) (3703833 / 1000000) (370401 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8431 / 102400) (42159 / 512000) (3703833 / 1000000) (370401 / 100000) (32649 / 1000) (4082 / 125)
    (50451 / 1000) (6319 / 125) (-554251 / 1000) (48783 / 125000) (3011679 / 1000) (956131 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3703833 / 1000000) (535491499 / 8000) (956131 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3703833 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3703833 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell505 :
    ∀ t ∈ Set.Icc ((42159 / 512000) : ℝ) (42163 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((117902001 / 100000000) : ℝ) ≤ Real.exp (2 * (42159 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42159 / 512000)) (117902001 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42163 / 512000) : ℝ)) ≤ (1179038433 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42163 / 512000)) (1179038433 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66948085323 / 1000000) : ℝ) ≤ Real.exp (3 * (3703891 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3703891 / 1000000)) (66948085323 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42159 / 512000) : ℝ) (42163 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3703891 / 1000000) (926017 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42159 / 512000) (42163 / 512000) (117902001 / 100000000) (1179038433 / 1000000000) (3703891 / 1000000) (926017 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42159 / 512000) (42163 / 512000) (3703891 / 1000000) (926017 / 250000) (653 / 20) (16329 / 500)
    (25229 / 500) (50559 / 1000) (-554261 / 1000) (195107 / 500000) (3011867 / 1000) (3823859 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3703891 / 1000000) (66948085323 / 1000000) (3823859 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3703891 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3703891 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell506 :
    ∀ t ∈ Set.Icc ((42163 / 512000) : ℝ) (42167 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((36844951 / 31250000) : ℝ) ≤ Real.exp (2 * (42163 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42163 / 512000)) (36844951 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42167 / 512000) : ℝ)) ≤ (147382107 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42167 / 512000)) (147382107 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((33479867649 / 500000) : ℝ) ≤ Real.exp (3 * (3703949 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3703949 / 1000000)) (33479867649 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42163 / 512000) : ℝ) (42167 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3703949 / 1000000) (1852063 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42163 / 512000) (42167 / 512000) (36844951 / 31250000) (147382107 / 125000000) (3703949 / 1000000) (1852063 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42163 / 512000) (42167 / 512000) (3703949 / 1000000) (1852063 / 500000) (8163 / 250) (32659 / 1000)
    (10093 / 200) (25283 / 500) (-554271 / 1000) (78033 / 200000) (376507 / 125) (1911597 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3703949 / 1000000) (33479867649 / 500000) (1911597 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3703949 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3703949 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell507 :
    ∀ t ∈ Set.Icc ((42167 / 512000) : ℝ) (42171 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((235811371 / 200000000) : ℝ) ≤ Real.exp (2 * (42167 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42167 / 512000)) (235811371 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42171 / 512000) : ℝ)) ≤ (1179075279 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42171 / 512000)) (1179075279 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((669713873 / 10000) : ℝ) ≤ Real.exp (3 * (3704007 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3704007 / 1000000)) (669713873 / 10000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42167 / 512000) : ℝ) (42171 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3704007 / 1000000) (3704183 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42167 / 512000) (42171 / 512000) (235811371 / 200000000) (1179075279 / 1000000000) (3704007 / 1000000) (3704183 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42167 / 512000) (42171 / 512000) (3704007 / 1000000) (3704183 / 1000000) (32653 / 1000) (1633 / 50)
    (6309 / 125) (50573 / 1000) (-277143 / 500) (78023 / 200000) (1506121 / 500) (59727 / 15625000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3704007 / 1000000) (669713873 / 10000) (59727 / 15625000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3704007 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3704007 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell508 :
    ∀ t ∈ Set.Icc ((42171 / 512000) : ℝ) (1687 / 20480), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((589537639 / 500000000) : ℝ) ≤ Real.exp (2 * (42171 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42171 / 512000)) (589537639 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1687 / 20480) : ℝ)) ≤ (589546851 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1687 / 20480)) (589546851 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66982840381 / 1000000) : ℝ) ≤ Real.exp (3 * (57876 / 15625)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (57876 / 15625)) (66982840381 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42171 / 512000) : ℝ) (1687 / 20480),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (57876 / 15625) (3704241 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42171 / 512000) (1687 / 20480) (589537639 / 500000000) (589546851 / 500000000) (57876 / 15625) (3704241 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42171 / 512000) (1687 / 20480) (57876 / 15625) (3704241 / 1000000) (16327 / 500) (16331 / 500)
    (50479 / 1000) (2529 / 50) (-554291 / 1000) (195033 / 500000) (301243 / 100) (1223 / 320000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (57876 / 15625) (66982840381 / 1000000) (1223 / 320000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (57876 / 15625)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (57876 / 15625)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell509 :
    ∀ t ∈ Set.Icc ((1687 / 20480) : ℝ) (42179 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1179093701 / 1000000000) : ℝ) ≤ Real.exp (2 * (1687 / 20480)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1687 / 20480)) (1179093701 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42179 / 512000) : ℝ)) ≤ (9432897 / 8000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42179 / 512000)) (9432897 / 8000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16748624101 / 250000) : ℝ) ≤ Real.exp (3 * (1852061 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1852061 / 500000)) (16748624101 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1687 / 20480) : ℝ) (42179 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1852061 / 500000) (3704299 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1687 / 20480) (42179 / 512000) (1179093701 / 1000000000) (9432897 / 8000000) (1852061 / 500000) (3704299 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1687 / 20480) (42179 / 512000) (1852061 / 500000) (3704299 / 1000000) (4082 / 125) (32663 / 1000)
    (25243 / 500) (12647 / 250) (-554301 / 1000) (390017 / 1000000) (3012619 / 1000) (382121 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1852061 / 500000) (16748624101 / 250000) (382121 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1852061 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1852061 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell510 :
    ∀ t ∈ Set.Icc ((42179 / 512000) : ℝ) (42183 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((294778031 / 250000000) : ℝ) ≤ Real.exp (2 * (42179 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42179 / 512000)) (294778031 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42183 / 512000) : ℝ)) ≤ (1179130549 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42183 / 512000)) (1179130549 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((13401230891 / 200000) : ℝ) ≤ Real.exp (3 * (185209 / 50000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (185209 / 50000)) (13401230891 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42179 / 512000) : ℝ) (42183 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (185209 / 50000) (3704357 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42179 / 512000) (42183 / 512000) (294778031 / 250000000) (1179130549 / 1000000000) (185209 / 50000) (3704357 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42179 / 512000) (42183 / 512000) (185209 / 50000) (3704357 / 1000000) (32657 / 1000) (4083 / 125)
    (50493 / 1000) (10119 / 200) (-554311 / 1000) (389967 / 1000000) (376601 / 125) (764109 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (185209 / 50000) (13401230891 / 200000) (764109 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (185209 / 50000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (185209 / 50000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell511 :
    ∀ t ∈ Set.Icc ((42183 / 512000) : ℝ) (42187 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((294782637 / 250000000) : ℝ) ≤ Real.exp (2 * (42183 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42183 / 512000)) (294782637 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42187 / 512000) : ℝ)) ≤ (1179148973 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42187 / 512000)) (1179148973 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((33508907267 / 500000) : ℝ) ≤ Real.exp (3 * (1852119 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1852119 / 500000)) (33508907267 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42183 / 512000) : ℝ) (42187 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1852119 / 500000) (740883 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42183 / 512000) (42187 / 512000) (294782637 / 250000000) (1179148973 / 1000000000) (1852119 / 500000) (740883 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42183 / 512000) (42187 / 512000) (1852119 / 500000) (740883 / 200000) (32659 / 1000) (16333 / 500)
    (101 / 2) (25301 / 500) (-554321 / 1000) (194959 / 500000) (753249 / 250) (95497 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1852119 / 500000) (33508907267 / 500000) (95497 / 25000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1852119 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1852119 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell512 :
    ∀ t ∈ Set.Icc ((42187 / 512000) : ℝ) (42191 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((294787243 / 250000000) : ℝ) ≤ Real.exp (2 * (42187 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42187 / 512000)) (294787243 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42191 / 512000) : ℝ)) ≤ (589583699 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42191 / 512000)) (589583699 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((67029476643 / 1000000) : ℝ) ≤ Real.exp (3 * (463037 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (463037 / 125000)) (67029476643 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42187 / 512000) : ℝ) (42191 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (463037 / 125000) (3704473 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42187 / 512000) (42191 / 512000) (294787243 / 250000000) (589583699 / 500000000) (463037 / 125000) (3704473 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42187 / 512000) (42191 / 512000) (463037 / 125000) (3704473 / 1000000) (1633 / 50) (32667 / 1000)
    (50507 / 1000) (50609 / 1000) (-554331 / 1000) (97467 / 250000) (602637 / 200) (238701 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (463037 / 125000) (67029476643 / 1000000) (238701 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (463037 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (463037 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell513 :
    ∀ t ∈ Set.Icc ((42191 / 512000) : ℝ) (42199 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1179167397 / 1000000000) : ℝ) ≤ Real.exp (2 * (42191 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42191 / 512000)) (1179167397 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42199 / 512000) : ℝ)) ≤ (1179204247 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42199 / 512000)) (1179204247 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((67041140781 / 1000000) : ℝ) ≤ Real.exp (3 * (1852177 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1852177 / 500000)) (67041140781 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42191 / 512000) : ℝ) (42199 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1852177 / 500000) (3704589 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42191 / 512000) (42199 / 512000) (1179167397 / 1000000000) (1179204247 / 1000000000) (1852177 / 500000) (3704589 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42191 / 512000) (42199 / 512000) (1852177 / 500000) (3704589 / 1000000) (32661 / 1000) (3267 / 100)
    (25251 / 500) (12659 / 250) (-277041 / 500) (389837 / 1000000) (1506781 / 500) (3818551 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1852177 / 500000) (67041140781 / 1000000) (3818551 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1852177 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1852177 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell514 :
    ∀ t ∈ Set.Icc ((42199 / 512000) : ℝ) (42207 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((589602123 / 500000000) : ℝ) ≤ Real.exp (2 * (42199 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42199 / 512000)) (589602123 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42207 / 512000) : ℝ)) ≤ (589620549 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42207 / 512000)) (589620549 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((67064475147 / 1000000) : ℝ) ≤ Real.exp (3 * (370447 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (370447 / 100000)) (67064475147 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42199 / 512000) : ℝ) (42207 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (370447 / 100000) (57886 / 15625) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42199 / 512000) (42207 / 512000) (589602123 / 500000000) (589620549 / 500000000) (370447 / 100000) (57886 / 15625) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42199 / 512000) (42207 / 512000) (370447 / 100000) (57886 / 15625) (4083 / 125) (32673 / 1000)
    (12629 / 250) (1013 / 20) (-277053 / 500) (194869 / 500000) (3013937 / 1000) (3817223 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (370447 / 100000) (67064475147 / 1000000) (3817223 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (370447 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (370447 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell515 :
    ∀ t ∈ Set.Icc ((42207 / 512000) : ℝ) (42211 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1179241097 / 1000000000) : ℝ) ≤ Real.exp (2 * (42207 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42207 / 512000)) (1179241097 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42211 / 512000) : ℝ)) ≤ (294814881 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42211 / 512000)) (294814881 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((67087616371 / 1000000) : ℝ) ≤ Real.exp (3 * (740917 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (740917 / 200000)) (67087616371 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42207 / 512000) : ℝ) (42211 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (740917 / 200000) (1852381 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42207 / 512000) (42211 / 512000) (1179241097 / 1000000000) (294814881 / 250000000) (740917 / 200000) (1852381 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42207 / 512000) (42211 / 512000) (740917 / 200000) (1852381 / 500000) (32667 / 1000) (16337 / 500)
    (50543 / 1000) (12661 / 250) (-554381 / 1000) (389621 / 1000000) (24113 / 8) (1907953 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (740917 / 200000) (67087616371 / 1000000) (1907953 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (740917 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (740917 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell516 :
    ∀ t ∈ Set.Icc ((42211 / 512000) : ℝ) (42219 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1179259523 / 1000000000) : ℝ) ≤ Real.exp (2 * (42211 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42211 / 512000)) (1179259523 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42219 / 512000) : ℝ)) ≤ (147412047 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42219 / 512000)) (147412047 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((67099290627 / 1000000) : ℝ) ≤ Real.exp (3 * (3704643 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3704643 / 1000000)) (67099290627 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42211 / 512000) : ℝ) (42219 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3704643 / 1000000) (1852439 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42211 / 512000) (42219 / 512000) (1179259523 / 1000000000) (147412047 / 125000000) (3704643 / 1000000) (1852439 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42211 / 512000) (42219 / 512000) (3704643 / 1000000) (1852439 / 500000) (8167 / 250) (32677 / 1000)
    (50537 / 1000) (50671 / 1000) (-554131 / 1000) (38959 / 100000) (3014503 / 1000) (1907621 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3704643 / 1000000) (67099290627 / 1000000) (1907621 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3704643 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3704643 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell517 :
    ∀ t ∈ Set.Icc ((42219 / 512000) : ℝ) (42227 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((9434371 / 8000000) : ℝ) ≤ Real.exp (2 * (42219 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42219 / 512000)) (9434371 / 8000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42227 / 512000) : ℝ)) ≤ (117933323 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42227 / 512000)) (117933323 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4195165327 / 62500) : ℝ) ≤ Real.exp (3 * (3704759 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3704759 / 1000000)) (4195165327 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42219 / 512000) : ℝ) (42227 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3704759 / 1000000) (1852497 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42219 / 512000) (42227 / 512000) (9434371 / 8000000) (117933323 / 100000000) (3704759 / 1000000) (1852497 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42219 / 512000) (42227 / 512000) (3704759 / 1000000) (1852497 / 500000) (3267 / 100) (817 / 25)
    (50551 / 1000) (10137 / 200) (-554151 / 1000) (389491 / 1000000) (75372 / 25) (762783 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3704759 / 1000000) (4195165327 / 62500) (762783 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3704759 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3704759 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell518 :
    ∀ t ∈ Set.Icc ((42227 / 512000) : ℝ) (8447 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1179333229 / 1000000000) : ℝ) ≤ Real.exp (2 * (42227 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42227 / 512000)) (1179333229 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8447 / 102400) : ℝ)) ≤ (294842521 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8447 / 102400)) (294842521 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((33573003983 / 500000) : ℝ) ≤ Real.exp (3 * (29639 / 8000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (29639 / 8000)) (33573003983 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42227 / 512000) : ℝ) (8447 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (29639 / 8000) (370511 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42227 / 512000) (8447 / 102400) (1179333229 / 1000000000) (294842521 / 250000000) (29639 / 8000) (370511 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42227 / 512000) (8447 / 102400) (29639 / 8000) (370511 / 100000) (32673 / 1000) (32683 / 1000)
    (10113 / 200) (50699 / 1000) (-554171 / 1000) (24337 / 62500) (1507629 / 500) (953147 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (29639 / 8000) (33573003983 / 500000) (953147 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (29639 / 8000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (29639 / 8000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell519 :
    ∀ t ∈ Set.Icc ((8447 / 102400) : ℝ) (42243 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1179370083 / 1000000000) : ℝ) ≤ Real.exp (2 * (8447 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8447 / 102400)) (1179370083 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42243 / 512000) : ℝ)) ≤ (58970347 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42243 / 512000)) (58970347 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4198086177 / 62500) : ℝ) ≤ Real.exp (3 * (3704991 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3704991 / 1000000)) (4198086177 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8447 / 102400) : ℝ) (42243 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3704991 / 1000000) (148209 / 40000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8447 / 102400) (42243 / 512000) (1179370083 / 1000000000) (58970347 / 50000000) (3704991 / 1000000) (148209 / 40000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8447 / 102400) (42243 / 512000) (3704991 / 1000000) (148209 / 40000) (8169 / 250) (6537 / 200)
    (2529 / 50) (50713 / 1000) (-110839 / 200) (389293 / 1000000) (376954 / 125) (3811261 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3704991 / 1000000) (4198086177 / 62500) (3811261 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3704991 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3704991 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch025 :
    ∀ t ∈ Set.Icc ((42139 / 512000) : ℝ) (42243 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell500
      hpThetaDensityLowerExpCompact_cell501)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell502
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell503
      hpThetaDensityLowerExpCompact_cell504)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell505
      hpThetaDensityLowerExpCompact_cell506)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell507
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell508
      hpThetaDensityLowerExpCompact_cell509))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell510
      hpThetaDensityLowerExpCompact_cell511)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell512
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell513
      hpThetaDensityLowerExpCompact_cell514)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell515
      hpThetaDensityLowerExpCompact_cell516)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell517
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell518
      hpThetaDensityLowerExpCompact_cell519)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch025
end HodgeProofHP
