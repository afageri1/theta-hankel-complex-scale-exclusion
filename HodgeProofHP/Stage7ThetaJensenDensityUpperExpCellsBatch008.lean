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
theorem hpThetaDensityUpperExpCompact_cell160 :
    ∀ t ∈ Set.Icc ((667 / 2000) : ℝ) (669 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1948383393 / 1000000000) : ℝ) ≤ Real.exp (2 * (667 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (667 / 2000)) (1948383393 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((669 / 2000) : ℝ)) ≤ (1952284061 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (669 / 2000)) (1952284061 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((47060614305521 / 500000) : ℝ) ≤ Real.exp (3 * (3060423 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3060423 / 500000)) (47060614305521 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((667 / 2000) : ℝ) (669 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3060423 / 500000) (383331 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (667 / 2000) (669 / 2000) (1948383393 / 1000000000) (1952284061 / 1000000000) (3060423 / 500000) (383331 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (667 / 2000) (669 / 2000) (3060423 / 500000) (383331 / 62500) (113059 / 1000) (22749 / 200)
    (797821 / 1000) (813803 / 1000) (2934939 / 1000) (1261 / 1000000) (4528201 / 200) (17 / 6250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3060423 / 500000) (47060614305521 / 500000) (17 / 6250000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3060423 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3060423 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell161 :
    ∀ t ∈ Set.Icc ((669 / 2000) : ℝ) (671 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((97614203 / 50000000) : ℝ) ≤ Real.exp (2 * (669 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (669 / 2000)) (97614203 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((671 / 2000) : ℝ)) ≤ (244524067 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (671 / 2000)) (244524067 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((24409639673729 / 250000) : ℝ) ≤ Real.exp (3 * (61331 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (61331 / 10000)) (24409639673729 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((669 / 2000) : ℝ) (671 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (61331 / 10000) (245823 / 40000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (669 / 2000) (671 / 2000) (97614203 / 50000000) (244524067 / 125000000) (61331 / 10000) (245823 / 40000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (669 / 2000) (671 / 2000) (61331 / 10000) (245823 / 40000) (56793 / 500) (57137 / 500)
    (402261 / 500) (82059 / 100) (2986649 / 1000) (1223 / 1000000) (22822861 / 1000) (1311 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (61331 / 10000) (24409639673729 / 250000) (1311 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (61331 / 10000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (61331 / 10000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell162 :
    ∀ t ∈ Set.Icc ((671 / 2000) : ℝ) (673 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((391238507 / 200000000) : ℝ) ≤ Real.exp (2 * (671 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (671 / 2000)) (391238507 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((673 / 2000) : ℝ)) ≤ (490027209 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (673 / 2000)) (490027209 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((101294420589573 / 1000000) : ℝ) ≤ Real.exp (3 * (3072689 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3072689 / 500000)) (101294420589573 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((671 / 2000) : ℝ) (673 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3072689 / 500000) (3078939 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (671 / 2000) (673 / 2000) (391238507 / 200000000) (490027209 / 250000000) (3072689 / 500000) (3078939 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (671 / 2000) (673 / 2000) (3072689 / 500000) (3078939 / 500000) (22823 / 200) (57403 / 500)
    (811271 / 1000) (413713 / 500) (607797 / 200) (593 / 500000) (23006169 / 1000) (79 / 31250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3072689 / 500000) (101294420589573 / 1000000) (79 / 31250000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3072689 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3072689 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell163 :
    ∀ t ∈ Set.Icc ((673 / 2000) : ℝ) (27 / 80), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((392021767 / 200000000) : ℝ) ≤ Real.exp (2 * (673 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (673 / 2000)) (392021767 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((27 / 80) : ℝ)) ≤ (122752061 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (27 / 80)) (122752061 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((26273707993873 / 250000) : ℝ) ≤ Real.exp (3 * (6157681 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6157681 / 1000000)) (26273707993873 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((673 / 2000) : ℝ) (27 / 80),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6157681 / 1000000) (3085103 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (673 / 2000) (27 / 80) (392021767 / 200000000) (122752061 / 62500000) (6157681 / 1000000) (3085103 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (673 / 2000) (27 / 80) (6157681 / 1000000) (3085103 / 500000) (57323 / 500) (5767 / 50)
    (81807 / 100) (104289 / 125) (1545979 / 500) (23 / 20000) (5797739 / 250) (609 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6157681 / 1000000) (26273707993873 / 250000) (609 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6157681 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6157681 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell164 :
    ∀ t ∈ Set.Icc ((27 / 80) : ℝ) (677 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((78561319 / 40000000) : ℝ) ≤ Real.exp (2 * (27 / 80)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (27 / 80)) (78561319 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((677 / 2000) : ℝ)) ≤ (1967964973 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (677 / 2000)) (1967964973 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((27261443809377 / 250000) : ℝ) ≤ Real.exp (3 * (6170009 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6170009 / 1000000)) (27261443809377 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((27 / 80) : ℝ) (677 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6170009 / 1000000) (6182559 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (27 / 80) (677 / 2000) (78561319 / 40000000) (1967964973 / 1000000000) (6170009 / 1000000) (6182559 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (27 / 80) (677 / 2000) (6170009 / 1000000) (6182559 / 1000000) (5759 / 50) (115877 / 1000)
    (412459 / 500) (841247 / 1000) (1572787 / 500) (223 / 200000) (23377231 / 1000) (587 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6170009 / 1000000) (27261443809377 / 250000) (587 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6170009 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6170009 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell165 :
    ∀ t ∈ Set.Icc ((677 / 2000) : ℝ) (679 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((491991243 / 250000000) : ℝ) ≤ Real.exp (2 * (677 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (677 / 2000)) (491991243 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((679 / 2000) : ℝ)) ≤ (985952421 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (679 / 2000)) (985952421 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4526126061283 / 40000) : ℝ) ≤ Real.exp (3 * (6182361 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6182361 / 1000000)) (4526126061283 / 40000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((677 / 2000) : ℝ) (679 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6182361 / 1000000) (6194937 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (677 / 2000) (679 / 2000) (491991243 / 250000000) (985952421 / 500000000) (6182361 / 1000000) (6194937 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (677 / 2000) (679 / 2000) (6182361 / 1000000) (6194937 / 1000000) (28929 / 250) (23283 / 200)
    (166363 / 200) (424117 / 500) (3199853 / 1000) (1081 / 1000000) (23565007 / 1000) (2263 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6182361 / 1000000) (4526126061283 / 40000) (2263 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6182361 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6182361 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell166 :
    ∀ t ∈ Set.Icc ((679 / 2000) : ℝ) (681 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1971904841 / 1000000000) : ℝ) ≤ Real.exp (2 * (679 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (679 / 2000)) (1971904841 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((681 / 2000) : ℝ)) ≤ (987926299 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (681 / 2000)) (987926299 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1834752098457 / 15625) : ℝ) ≤ Real.exp (3 * (6194739 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6194739 / 1000000)) (1834752098457 / 15625) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((679 / 2000) : ℝ) (681 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6194739 / 1000000) (6207339 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (679 / 2000) (681 / 2000) (1971904841 / 1000000000) (987926299 / 500000000) (6194739 / 1000000) (6207339 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (679 / 2000) (681 / 2000) (6194739 / 1000000) (6207339 / 1000000) (23251 / 200) (29239 / 250)
    (838763 / 1000) (85527 / 100) (3254757 / 1000) (131 / 125000) (23754279 / 1000) (2181 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6194739 / 1000000) (1834752098457 / 15625) (2181 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6194739 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6194739 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell167 :
    ∀ t ∈ Set.Icc ((681 / 2000) : ℝ) (683 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1975852597 / 1000000000) : ℝ) ≤ Real.exp (2 * (681 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (681 / 2000)) (1975852597 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((683 / 2000) : ℝ)) ≤ (1979808257 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (683 / 2000)) (1979808257 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((121864457349249 / 1000000) : ℝ) ≤ Real.exp (3 * (310357 / 50000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (310357 / 50000)) (121864457349249 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((681 / 2000) : ℝ) (683 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (310357 / 50000) (3109883 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (681 / 2000) (683 / 2000) (1975852597 / 1000000000) (1979808257 / 1000000000) (310357 / 50000) (3109883 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (681 / 2000) (683 / 2000) (310357 / 50000) (3109883 / 500000) (23359 / 200) (235 / 2)
    (845761 / 1000) (862357 / 1000) (66207 / 20) (127 / 125000) (11972537 / 500) (2101 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (310357 / 50000) (121864457349249 / 1000000) (2101 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (310357 / 50000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (310357 / 50000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell168 :
    ∀ t ∈ Set.Icc ((683 / 2000) : ℝ) (137 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((3866813 / 1953125) : ℝ) ≤ Real.exp (2 * (683 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (683 / 2000)) (3866813 / 1953125) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((137 / 400) : ℝ)) ≤ (495942959 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (137 / 400)) (495942959 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((126482256667613 / 1000000) : ℝ) ≤ Real.exp (3 * (6219567 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6219567 / 1000000)) (126482256667613 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((683 / 2000) : ℝ) (137 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6219567 / 1000000) (3116109 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (683 / 2000) (137 / 400) (3866813 / 1953125) (495942959 / 250000000) (6219567 / 1000000) (3116109 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (683 / 2000) (137 / 400) (6219567 / 1000000) (3116109 / 500000) (58669 / 500) (23609 / 200)
    (85281 / 100) (173899 / 200) (16833 / 5) (123 / 125000) (24137403 / 1000) (253 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6219567 / 1000000) (126482256667613 / 1000000) (253 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6219567 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6219567 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell169 :
    ∀ t ∈ Set.Icc ((137 / 400) : ℝ) (687 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((396754367 / 200000000) : ℝ) ≤ Real.exp (2 * (137 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (137 / 400)) (396754367 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((687 / 2000) : ℝ)) ≤ (39754867 / 20000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (687 / 2000)) (39754867 / 20000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16410571109197 / 125000) : ℝ) ≤ Real.exp (3 * (6232019 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6232019 / 1000000)) (16410571109197 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((137 / 400) : ℝ) (687 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6232019 / 1000000) (1248939 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (137 / 400) (687 / 2000) (396754367 / 200000000) (39754867 / 20000000) (6232019 / 1000000) (1248939 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (137 / 400) (687 / 2000) (6232019 / 1000000) (1248939 / 200000) (29471 / 250) (118593 / 1000)
    (85991 / 100) (175337 / 200) (136941 / 40) (477 / 500000) (12165639 / 500) (39 / 20000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6232019 / 1000000) (16410571109197 / 125000) (39 / 20000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6232019 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6232019 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell170 :
    ∀ t ∈ Set.Icc ((687 / 2000) : ℝ) (689 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1987743349 / 1000000000) : ℝ) ≤ Real.exp (2 * (687 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (687 / 2000)) (1987743349 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((689 / 2000) : ℝ)) ≤ (398344563 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (689 / 2000)) (398344563 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((27255738891077 / 200000) : ℝ) ≤ Real.exp (3 * (1248899 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1248899 / 200000)) (27255738891077 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((687 / 2000) : ℝ) (689 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1248899 / 200000) (6257197 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (687 / 2000) (689 / 2000) (1987743349 / 1000000000) (398344563 / 200000000) (1248899 / 200000) (6257197 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (687 / 2000) (689 / 2000) (1248899 / 200000) (6257197 / 1000000) (118431 / 1000) (14893 / 125)
    (43353 / 50) (883927 / 1000) (1740573 / 500) (37 / 40000) (24526711 / 1000) (1879 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1248899 / 200000) (27255738891077 / 200000) (1879 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1248899 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1248899 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell171 :
    ∀ t ∈ Set.Icc ((689 / 2000) : ℝ) (691 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((995861407 / 500000000) : ℝ) ≤ Real.exp (2 * (689 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (689 / 2000)) (995861407 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((691 / 2000) : ℝ)) ≤ (997855123 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (691 / 2000)) (997855123 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8842092272209 / 62500) : ℝ) ≤ Real.exp (3 * (6256997 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6256997 / 1000000)) (8842092272209 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((689 / 2000) : ℝ) (691 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6256997 / 1000000) (1567431 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (689 / 2000) (691 / 2000) (995861407 / 500000000) (997855123 / 500000000) (6256997 / 1000000) (1567431 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (689 / 2000) (691 / 2000) (6256997 / 1000000) (1567431 / 250000) (118981 / 1000) (14962 / 125)
    (874263 / 1000) (891221 / 1000) (884861 / 250) (14 / 15625) (3090464 / 125) (181 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6256997 / 1000000) (8842092272209 / 62500) (181 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6256997 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6256997 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell172 :
    ∀ t ∈ Set.Icc ((691 / 2000) : ℝ) (693 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((399142049 / 200000000) : ℝ) ≤ Real.exp (2 * (691 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (691 / 2000)) (399142049 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((693 / 2000) : ℝ)) ≤ (1999705661 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (693 / 2000)) (1999705661 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((146876474614077 / 1000000) : ℝ) ≤ Real.exp (3 * (6269523 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6269523 / 1000000)) (146876474614077 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((691 / 2000) : ℝ) (693 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6269523 / 1000000) (1570569 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (691 / 2000) (693 / 2000) (399142049 / 200000000) (1999705661 / 1000000000) (6269523 / 1000000) (1570569 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (691 / 2000) (693 / 2000) (6269523 / 1000000) (1570569 / 250000) (59767 / 500) (120251 / 1000)
    (440759 / 500) (898567 / 1000) (3598451 / 1000) (217 / 250000) (4984459 / 200) (1743 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6269523 / 1000000) (146876474614077 / 1000000) (1743 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6269523 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6269523 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell173 :
    ∀ t ∈ Set.Icc ((693 / 2000) : ℝ) (139 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((99985283 / 50000000) : ℝ) ≤ Real.exp (2 * (693 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (693 / 2000)) (99985283 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((139 / 400) : ℝ)) ≤ (1001854537 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (139 / 400)) (1001854537 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((76248654509777 / 500000) : ℝ) ≤ Real.exp (3 * (251283 / 40000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (251283 / 40000)) (76248654509777 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((693 / 2000) : ℝ) (139 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (251283 / 40000) (6294853 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (693 / 2000) (139 / 400) (99985283 / 50000000) (1001854537 / 500000000) (251283 / 40000) (6294853 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (693 / 2000) (139 / 400) (251283 / 40000) (6294853 / 1000000) (15011 / 125) (120809 / 1000)
    (35553 / 40) (452983 / 500) (3658149 / 1000) (841 / 1000000) (3140309 / 125) (1679 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (251283 / 40000) (76248654509777 / 500000) (1679 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (251283 / 40000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (251283 / 40000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell174 :
    ∀ t ∈ Set.Icc ((139 / 400) : ℝ) (697 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2003709073 / 1000000000) : ℝ) ≤ Real.exp (2 * (139 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (139 / 400)) (2003709073 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((697 / 2000) : ℝ)) ≤ (2007720503 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (697 / 2000)) (2007720503 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31668939111997 / 200000) : ℝ) ≤ Real.exp (3 * (1573663 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1573663 / 250000)) (31668939111997 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((139 / 400) : ℝ) (697 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1573663 / 250000) (1261491 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (139 / 400) (697 / 2000) (2003709073 / 1000000000) (2007720503 / 1000000000) (1573663 / 250000) (1261491 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (139 / 400) (697 / 2000) (1573663 / 250000) (1261491 / 200000) (24129 / 200) (121369 / 1000)
    (448093 / 500) (913419 / 1000) (3718557 / 1000) (163 / 200000) (6331063 / 250) (1617 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1573663 / 250000) (31668939111997 / 200000) (1617 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1573663 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1573663 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell175 :
    ∀ t ∈ Set.Icc ((697 / 2000) : ℝ) (699 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1003860251 / 500000000) : ℝ) ≤ Real.exp (2 * (697 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (697 / 2000)) (1003860251 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((699 / 2000) : ℝ)) ≤ (1005869981 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (699 / 2000)) (1005869981 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((82213840270489 / 500000) : ℝ) ≤ Real.exp (3 * (6307253 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6307253 / 1000000)) (82213840270489 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((697 / 2000) : ℝ) (699 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6307253 / 1000000) (6320083 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (697 / 2000) (699 / 2000) (1003860251 / 500000000) (1005869981 / 500000000) (6307253 / 1000000) (6320083 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (697 / 2000) (699 / 2000) (6307253 / 1000000) (6320083 / 1000000) (24241 / 200) (121931 / 1000)
    (451799 / 500) (460463 / 500) (3779713 / 1000) (79 / 100000) (25527667 / 1000) (1557 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6307253 / 1000000) (82213840270489 / 500000) (1557 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6307253 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6307253 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell176 :
    ∀ t ∈ Set.Icc ((699 / 2000) : ℝ) (701 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2011739961 / 1000000000) : ℝ) ≤ Real.exp (2 * (699 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (699 / 2000)) (2011739961 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((701 / 2000) : ℝ)) ≤ (503941867 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (701 / 2000)) (503941867 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((10672355914647 / 62500) : ℝ) ≤ Real.exp (3 * (6319881 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6319881 / 1000000)) (10672355914647 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((699 / 2000) : ℝ) (701 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6319881 / 1000000) (98949 / 15625) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (699 / 2000) (701 / 2000) (2011739961 / 1000000000) (503941867 / 250000000) (6319881 / 1000000) (98949 / 15625) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (699 / 2000) (701 / 2000) (6319881 / 1000000) (98949 / 15625) (121767 / 1000) (24499 / 200)
    (182213 / 200) (464243 / 500) (480196 / 125) (153 / 200000) (2573271 / 100) (3 / 2000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6319881 / 1000000) (10672355914647 / 62500) (3 / 2000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6319881 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6319881 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell177 :
    ∀ t ∈ Set.Icc ((701 / 2000) : ℝ) (703 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2015767467 / 1000000000) : ℝ) ≤ Real.exp (2 * (701 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (701 / 2000)) (2015767467 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((703 / 2000) : ℝ)) ≤ (2019803037 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (703 / 2000)) (2019803037 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((177343652912903 / 1000000) : ℝ) ≤ Real.exp (3 * (6332533 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6332533 / 1000000)) (177343652912903 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((701 / 2000) : ℝ) (703 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6332533 / 1000000) (3172707 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (701 / 2000) (703 / 2000) (2015767467 / 1000000000) (2019803037 / 1000000000) (6332533 / 1000000) (3172707 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (701 / 2000) (703 / 2000) (6332533 / 1000000) (3172707 / 500000) (122331 / 1000) (61531 / 500)
    (183717 / 200) (936101 / 1000) (488021 / 125) (741 / 1000000) (5187879 / 200) (361 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6332533 / 1000000) (177343652912903 / 1000000) (361 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6332533 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6332533 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell178 :
    ∀ t ∈ Set.Icc ((703 / 2000) : ℝ) (141 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((504950759 / 250000000) : ℝ) ≤ Real.exp (2 * (703 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (703 / 2000)) (504950759 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((141 / 400) : ℝ)) ≤ (404769337 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (141 / 400)) (404769337 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((46049361054357 / 250000) : ℝ) ≤ Real.exp (3 * (6345211 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6345211 / 1000000)) (46049361054357 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((703 / 2000) : ℝ) (141 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6345211 / 1000000) (6358117 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (703 / 2000) (141 / 400) (504950759 / 250000000) (404769337 / 200000000) (6345211 / 1000000) (6358117 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (703 / 2000) (141 / 400) (6345211 / 1000000) (6358117 / 1000000) (61449 / 500) (15454 / 125)
    (23154 / 25) (943769 / 1000) (3967493 / 1000) (359 / 500000) (13073867 / 500) (139 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6345211 / 1000000) (46049361054357 / 250000) (139 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6345211 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6345211 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell179 :
    ∀ t ∈ Set.Icc ((141 / 400) : ℝ) (707 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((505961671 / 250000000) : ℝ) ≤ Real.exp (2 * (141 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (141 / 400)) (505961671 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((707 / 2000) : ℝ)) ≤ (2027898429 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (707 / 2000)) (2027898429 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((7653195290027 / 40000) : ℝ) ≤ Real.exp (3 * (3178957 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3178957 / 500000)) (7653195290027 / 40000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((141 / 400) : ℝ) (707 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3178957 / 500000) (3185423 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (141 / 400) (707 / 2000) (505961671 / 250000000) (2027898429 / 1000000000) (3178957 / 500000) (3185423 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (141 / 400) (707 / 2000) (3178957 / 500000) (3185423 / 500000) (123467 / 1000) (31051 / 250)
    (933789 / 1000) (475747 / 500) (4031583 / 1000) (87 / 125000) (5271551 / 200) (1339 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3178957 / 500000) (7653195290027 / 40000) (1339 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3178957 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3178957 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityUpperExpCompact_cellsBatch008 :
    ∀ t ∈ Set.Icc ((667 / 2000) : ℝ) (707 / 2000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell160
      hpThetaDensityUpperExpCompact_cell161)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell162
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell163
      hpThetaDensityUpperExpCompact_cell164)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell165
      hpThetaDensityUpperExpCompact_cell166)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell167
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell168
      hpThetaDensityUpperExpCompact_cell169))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell170
      hpThetaDensityUpperExpCompact_cell171)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell172
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell173
      hpThetaDensityUpperExpCompact_cell174)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell175
      hpThetaDensityUpperExpCompact_cell176)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell177
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell178
      hpThetaDensityUpperExpCompact_cell179)))))

#print axioms hpThetaDensityUpperExpCompact_cellsBatch008
end HodgeProofHP
