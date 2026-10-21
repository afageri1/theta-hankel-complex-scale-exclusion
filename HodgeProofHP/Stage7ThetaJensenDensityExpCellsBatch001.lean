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
theorem hpThetaDensityExpCompact_cell020 :
    ∀ t ∈ Set.Icc ((1621 / 16000) : ℝ) (1623 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((38269161 / 31250000) : ℝ) ≤ Real.exp (2 * (1621 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1621 / 16000)) (38269161 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1623 / 16000) : ℝ)) ≤ (76557459 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1623 / 16000)) (76557459 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((51442412949 / 500000) : ℝ) ≤ Real.exp (3 * (1923561 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1923561 / 500000)) (51442412949 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1621 / 16000) : ℝ) (1623 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1923561 / 500000) (3848207 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1621 / 16000) (1623 / 16000) (38269161 / 31250000) (76557459 / 62500000) (1923561 / 500000) (3848207 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1621 / 16000) (1623 / 16000) (1923561 / 500000) (3848207 / 1000000) (4514 / 125) (36153 / 1000)
    (13791 / 200) (69609 / 1000) (-569211 / 1000) (284727 / 1000000) (3508761 / 1000) (124411 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1923561 / 500000) (51442412949 / 500000) (124411 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1923561 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1923561 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell021 :
    ∀ t ∈ Set.Icc ((1623 / 16000) : ℝ) (13 / 128), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1224919343 / 1000000000) : ℝ) ≤ Real.exp (2 * (1623 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1623 / 16000)) (1224919343 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((13 / 128) : ℝ)) ≤ (306306403 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (13 / 128)) (306306403 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((103182180081 / 1000000) : ℝ) ≤ Real.exp (3 * (962021 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (962021 / 250000)) (103182180081 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1623 / 16000) : ℝ) (13 / 128),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (962021 / 250000) (3849169 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1623 / 16000) (13 / 128) (1224919343 / 1000000000) (306306403 / 250000000) (962021 / 250000) (3849169 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1623 / 16000) (13 / 128) (962021 / 250000) (3849169 / 1000000) (7227 / 200) (4522 / 125)
    (69089 / 1000) (69743 / 1000) (-5693 / 10) (284119 / 1000000) (3512271 / 1000) (2481049 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (962021 / 250000) (103182180081 / 1000000) (2481049 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (962021 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (962021 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell022 :
    ∀ t ∈ Set.Icc ((13 / 128) : ℝ) (1627 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1225225611 / 1000000000) : ℝ) ≤ Real.exp (2 * (13 / 128)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (13 / 128)) (1225225611 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1627 / 16000) : ℝ)) ≤ (1225531957 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1627 / 16000)) (1225531957 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((51740196833 / 500000) : ℝ) ≤ Real.exp (3 * (1924523 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1924523 / 500000)) (51740196833 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((13 / 128) : ℝ) (1627 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1924523 / 500000) (962533 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (13 / 128) (1627 / 16000) (1225225611 / 1000000000) (1225531957 / 1000000000) (1924523 / 500000) (962533 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (13 / 128) (1627 / 16000) (1924523 / 500000) (962533 / 250000) (36159 / 1000) (181 / 5)
    (69223 / 1000) (34939 / 500) (-71173 / 125) (283513 / 1000000) (3515787 / 1000) (2473899 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1924523 / 500000) (51740196833 / 500000) (2473899 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1924523 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1924523 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell023 :
    ∀ t ∈ Set.Icc ((1627 / 16000) : ℝ) (1629 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((306382989 / 250000000) : ℝ) ≤ Real.exp (2 * (1627 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1627 / 16000)) (306382989 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1629 / 16000) : ℝ)) ≤ (612919189 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1629 / 16000)) (612919189 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6486216821 / 62500) : ℝ) ≤ Real.exp (3 * (481251 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (481251 / 125000)) (6486216821 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1627 / 16000) : ℝ) (1629 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (481251 / 125000) (1925547 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1627 / 16000) (1629 / 16000) (306382989 / 250000000) (612919189 / 500000000) (481251 / 125000) (1925547 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1627 / 16000) (1629 / 16000) (481251 / 125000) (1925547 / 500000) (36183 / 1000) (4528 / 125)
    (34679 / 500) (17503 / 250) (-569473 / 1000) (70727 / 250000) (1759651 / 500) (246677 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (481251 / 125000) (6486216821 / 62500) (246677 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (481251 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (481251 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell024 :
    ∀ t ∈ Set.Icc ((1629 / 16000) : ℝ) (1631 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1225838377 / 1000000000) : ℝ) ≤ Real.exp (2 * (1629 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1629 / 16000)) (1225838377 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1631 / 16000) : ℝ)) ≤ (306536219 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1631 / 16000)) (306536219 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((5203986061 / 50000) : ℝ) ≤ Real.exp (3 * (3850971 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3850971 / 1000000)) (5203986061 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1629 / 16000) : ℝ) (1631 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3850971 / 1000000) (3852057 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1629 / 16000) (1631 / 16000) (1225838377 / 1000000000) (306536219 / 250000000) (3850971 / 1000000) (3852057 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1629 / 16000) (1631 / 16000) (3850971 / 1000000) (3852057 / 1000000) (36207 / 1000) (4531 / 125)
    (17373 / 250) (70147 / 1000) (-569561 / 1000) (4411 / 15625) (3522823 / 1000) (1229827 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3850971 / 1000000) (5203986061 / 50000) (1229827 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3850971 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3850971 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell025 :
    ∀ t ∈ Set.Icc ((1631 / 16000) : ℝ) (1633 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((9809159 / 8000000) : ℝ) ≤ Real.exp (2 * (1631 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1631 / 16000)) (9809159 / 8000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1633 / 16000) : ℝ)) ≤ (1226451451 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1633 / 16000)) (1226451451 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((20876168397 / 200000) : ℝ) ≤ Real.exp (3 * (1925967 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1925967 / 500000)) (20876168397 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1631 / 16000) : ℝ) (1633 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1925967 / 500000) (192651 / 50000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1631 / 16000) (1633 / 16000) (9809159 / 8000000) (1226451451 / 1000000000) (1925967 / 500000) (192651 / 50000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1631 / 16000) (1633 / 16000) (1925967 / 500000) (192651 / 50000) (36231 / 1000) (4534 / 125)
    (69627 / 1000) (35141 / 500) (-71206 / 125) (2817 / 10000) (3526347 / 1000) (1226279 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1925967 / 500000) (20876168397 / 200000) (1226279 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1925967 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1925967 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell026 :
    ∀ t ∈ Set.Icc ((1633 / 16000) : ℝ) (327 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((24529029 / 20000000) : ℝ) ≤ Real.exp (2 * (1633 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1633 / 16000)) (24529029 / 20000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((327 / 3200) : ℝ)) ≤ (613379051 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (327 / 3200)) (613379051 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((104682833943 / 1000000) : ℝ) ≤ Real.exp (3 * (3852897 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3852897 / 1000000)) (104682833943 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1633 / 16000) : ℝ) (327 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3852897 / 1000000) (120437 / 31250) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1633 / 16000) (327 / 3200) (24529029 / 20000000) (613379051 / 500000000) (3852897 / 1000000) (120437 / 31250) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1633 / 16000) (327 / 3200) (3852897 / 1000000) (120437 / 31250) (7251 / 200) (4537 / 125)
    (34881 / 500) (35209 / 500) (-56973 / 100) (281099 / 1000000) (1764939 / 500) (2445483 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3852897 / 1000000) (104682833943 / 1000000) (2445483 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3852897 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3852897 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell027 :
    ∀ t ∈ Set.Icc ((327 / 3200) : ℝ) (1637 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1226758101 / 1000000000) : ℝ) ≤ Real.exp (2 * (327 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (327 / 3200)) (1226758101 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1637 / 16000) : ℝ)) ≤ (122706483 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1637 / 16000)) (122706483 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((52492849807 / 500000) : ℝ) ≤ Real.exp (3 * (192693 / 50000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (192693 / 50000)) (52492849807 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((327 / 3200) : ℝ) (1637 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (192693 / 50000) (3854947 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (327 / 3200) (1637 / 16000) (1226758101 / 1000000000) (122706483 / 100000000) (192693 / 50000) (3854947 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (327 / 3200) (1637 / 16000) (192693 / 50000) (3854947 / 1000000) (36279 / 1000) (908 / 25)
    (8737 / 125) (70553 / 1000) (-71227 / 125) (140249 / 500000) (3533407 / 1000) (609607 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (192693 / 50000) (52492849807 / 500000) (609607 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (192693 / 50000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (192693 / 50000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell028 :
    ∀ t ∈ Set.Icc ((1637 / 16000) : ℝ) (1639 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1227064829 / 1000000000) : ℝ) ≤ Real.exp (2 * (1637 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1637 / 16000)) (1227064829 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1639 / 16000) : ℝ)) ≤ (613685817 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1639 / 16000)) (613685817 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((26322439349 / 250000) : ℝ) ≤ Real.exp (3 * (481853 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (481853 / 125000)) (26322439349 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1637 / 16000) : ℝ) (1639 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (481853 / 125000) (3855911 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1637 / 16000) (1639 / 16000) (1227064829 / 1000000000) (613685817 / 500000000) (481853 / 125000) (3855911 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1637 / 16000) (1639 / 16000) (481853 / 125000) (3855911 / 1000000) (36303 / 1000) (4543 / 125)
    (8754 / 125) (8836 / 125) (-284951 / 500) (139949 / 500000) (3536943 / 1000) (1215693 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (481853 / 125000) (26322439349 / 250000) (1215693 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (481853 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (481853 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell029 :
    ∀ t ∈ Set.Icc ((1639 / 16000) : ℝ) (1641 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1227371633 / 1000000000) : ℝ) ≤ Real.exp (2 * (1639 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1639 / 16000)) (1227371633 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1641 / 16000) : ℝ)) ≤ (306919629 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1641 / 16000)) (306919629 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((105594379 / 1000) : ℝ) ≤ Real.exp (3 * (3855787 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3855787 / 1000000)) (105594379 / 1000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1639 / 16000) : ℝ) (1641 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3855787 / 1000000) (6171 / 1600) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1639 / 16000) (1641 / 16000) (1227371633 / 1000000000) (306919629 / 250000000) (3855787 / 1000000) (6171 / 1600) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1639 / 16000) (1641 / 16000) (3855787 / 1000000) (6171 / 1600) (36327 / 1000) (4546 / 125)
    (70167 / 1000) (8853 / 125) (-284991 / 500) (2793 / 10000) (3540481 / 1000) (606093 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3855787 / 1000000) (105594379 / 1000) (606093 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3855787 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3855787 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell030 :
    ∀ t ∈ Set.Icc ((1641 / 16000) : ℝ) (1643 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((245535703 / 200000000) : ℝ) ≤ Real.exp (2 * (1641 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1641 / 16000)) (245535703 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1643 / 16000) : ℝ)) ≤ (613992737 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1643 / 16000)) (613992737 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((52950258663 / 500000) : ℝ) ≤ Real.exp (3 * (241047 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (241047 / 62500)) (52950258663 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1641 / 16000) : ℝ) (1643 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (241047 / 62500) (48223 / 12500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1641 / 16000) (1643 / 16000) (245535703 / 200000000) (613992737 / 500000000) (241047 / 62500) (48223 / 12500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1641 / 16000) (1643 / 16000) (241047 / 62500) (48223 / 12500) (36351 / 1000) (4549 / 125)
    (35151 / 500) (1774 / 25) (-570067 / 1000) (278701 / 1000000) (1772013 / 500) (604341 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (241047 / 62500) (52950258663 / 500000) (604341 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (241047 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (241047 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell031 :
    ∀ t ∈ Set.Icc ((1643 / 16000) : ℝ) (329 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1227985473 / 1000000000) : ℝ) ≤ Real.exp (2 * (1643 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1643 / 16000)) (1227985473 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((329 / 3200) : ℝ)) ≤ (307073127 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (329 / 3200)) (307073127 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((53103612291 / 500000) : ℝ) ≤ Real.exp (3 * (964429 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (964429 / 250000)) (53103612291 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1643 / 16000) : ℝ) (329 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (964429 / 250000) (964701 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1643 / 16000) (329 / 3200) (1227985473 / 1000000000) (307073127 / 250000000) (964429 / 250000) (964701 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1643 / 16000) (329 / 3200) (964429 / 250000) (964701 / 250000) (291 / 8) (4552 / 125)
    (35219 / 500) (14219 / 200) (-71269 / 125) (55621 / 200000) (354757 / 100) (2410383 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (964429 / 250000) (53103612291 / 500000) (2410383 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (964429 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (964429 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell032 :
    ∀ t ∈ Set.Icc ((329 / 3200) : ℝ) (1647 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1228292507 / 1000000000) : ℝ) ≤ Real.exp (2 * (329 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (329 / 3200)) (1228292507 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1647 / 16000) : ℝ)) ≤ (61429981 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1647 / 16000)) (61429981 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((106514820117 / 1000000) : ℝ) ≤ Real.exp (3 * (96467 / 25000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (96467 / 25000)) (106514820117 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((329 / 3200) : ℝ) (1647 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (96467 / 25000) (3859769 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (329 / 3200) (1647 / 16000) (1228292507 / 1000000000) (61429981 / 50000000) (96467 / 25000) (3859769 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (329 / 3200) (1647 / 16000) (96467 / 25000) (3859769 / 1000000) (36399 / 1000) (911 / 25)
    (70573 / 1000) (8904 / 125) (-57023 / 100) (27751 / 100000) (88778 / 25) (1201711 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (96467 / 25000) (106514820117 / 1000000) (1201711 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (96467 / 25000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (96467 / 25000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell033 :
    ∀ t ∈ Set.Icc ((1647 / 16000) : ℝ) (1649 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1228599619 / 1000000000) : ℝ) ≤ Real.exp (2 * (1647 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1647 / 16000)) (1228599619 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1649 / 16000) : ℝ)) ≤ (153613351 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1649 / 16000)) (153613351 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((53411813487 / 500000) : ℝ) ≤ Real.exp (3 * (771929 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (771929 / 200000)) (53411813487 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1647 / 16000) : ℝ) (1649 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (771929 / 200000) (1930367 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1647 / 16000) (1649 / 16000) (1228599619 / 1000000000) (153613351 / 125000000) (771929 / 200000) (1930367 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1647 / 16000) (1649 / 16000) (771929 / 200000) (1930367 / 500000) (36423 / 1000) (4558 / 125)
    (70709 / 1000) (8921 / 125) (-570313 / 1000) (55383 / 200000) (444334 / 125) (1198237 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (771929 / 200000) (53411813487 / 500000) (1198237 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (771929 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (771929 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell034 :
    ∀ t ∈ Set.Icc ((1649 / 16000) : ℝ) (1651 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1228906807 / 1000000000) : ℝ) ≤ Real.exp (2 * (1649 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1649 / 16000)) (1228906807 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1651 / 16000) : ℝ)) ≤ (1229214073 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1651 / 16000)) (1229214073 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((107133329119 / 1000000) : ℝ) ≤ Real.exp (3 * (386061 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (386061 / 100000)) (107133329119 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1649 / 16000) : ℝ) (1651 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (386061 / 100000) (3861699 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1649 / 16000) (1651 / 16000) (1228906807 / 1000000000) (1229214073 / 1000000000) (386061 / 100000) (3861699 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1649 / 16000) (1651 / 16000) (386061 / 100000) (3861699 / 1000000) (36447 / 1000) (4561 / 125)
    (14169 / 200) (8938 / 125) (-142599 / 250) (138161 / 500000) (889557 / 250) (1194773 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (386061 / 100000) (107133329119 / 1000000) (1194773 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (386061 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (386061 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell035 :
    ∀ t ∈ Set.Icc ((1651 / 16000) : ℝ) (1653 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((153651759 / 125000000) : ℝ) ≤ Real.exp (2 * (1651 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1651 / 16000)) (153651759 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1653 / 16000) : ℝ)) ≤ (245904283 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1653 / 16000)) (245904283 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2686106287 / 25000) : ℝ) ≤ Real.exp (3 * (482697 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (482697 / 125000)) (2686106287 / 25000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1651 / 16000) : ℝ) (1653 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (482697 / 125000) (772533 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1651 / 16000) (1653 / 16000) (153651759 / 125000000) (245904283 / 200000000) (482697 / 125000) (772533 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1651 / 16000) (1653 / 16000) (482697 / 125000) (772533 / 200000) (36471 / 1000) (4564 / 125)
    (70981 / 1000) (71641 / 1000) (-285239 / 500) (275729 / 1000000) (3561789 / 1000) (2382631 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (482697 / 125000) (2686106287 / 25000) (2382631 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (482697 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (482697 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell036 :
    ∀ t ∈ Set.Icc ((1653 / 16000) : ℝ) (331 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((614760707 / 500000000) : ℝ) ≤ Real.exp (2 * (1653 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1653 / 16000)) (614760707 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((331 / 3200) : ℝ)) ≤ (614914417 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (331 / 3200)) (614914417 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((107755752931 / 1000000) : ℝ) ≤ Real.exp (3 * (3862541 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3862541 / 1000000)) (107755752931 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1653 / 16000) : ℝ) (331 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3862541 / 1000000) (3863631 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1653 / 16000) (331 / 3200) (614760707 / 500000000) (614914417 / 500000000) (3862541 / 1000000) (3863631 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1653 / 16000) (331 / 3200) (3862541 / 1000000) (3863631 / 1000000) (7299 / 200) (4567 / 125)
    (71117 / 1000) (35889 / 500) (-114111 / 200) (137569 / 500000) (1782677 / 500) (37121 / 15625000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3862541 / 1000000) (107755752931 / 1000000) (37121 / 15625000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3862541 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3862541 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell037 :
    ∀ t ∈ Set.Icc ((331 / 3200) : ℝ) (1657 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1229828833 / 1000000000) : ℝ) ≤ Real.exp (2 * (331 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (331 / 3200)) (1229828833 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1657 / 16000) : ℝ)) ≤ (123013633 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1657 / 16000)) (123013633 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((108068481687 / 1000000) : ℝ) ≤ Real.exp (3 * (3863507 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3863507 / 1000000)) (108068481687 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((331 / 3200) : ℝ) (1657 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3863507 / 1000000) (3864597 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (331 / 3200) (1657 / 16000) (1229828833 / 1000000000) (123013633 / 100000000) (3863507 / 1000000) (3864597 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (331 / 3200) (1657 / 16000) (3863507 / 1000000) (3864597 / 1000000) (36519 / 1000) (914 / 25)
    (35627 / 500) (35957 / 500) (-142659 / 250) (68637 / 250000) (3568921 / 1000) (2368869 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3863507 / 1000000) (108068481687 / 1000000) (2368869 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3863507 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3863507 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell038 :
    ∀ t ∈ Set.Icc ((1657 / 16000) : ℝ) (1659 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1230136329 / 1000000000) : ℝ) ≤ Real.exp (2 * (1657 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1657 / 16000)) (1230136329 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1659 / 16000) : ℝ)) ≤ (615221951 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1659 / 16000)) (615221951 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((108382118043 / 1000000) : ℝ) ≤ Real.exp (3 * (3864473 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3864473 / 1000000)) (108382118043 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1657 / 16000) : ℝ) (1659 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3864473 / 1000000) (3865563 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1657 / 16000) (1659 / 16000) (1230136329 / 1000000000) (615221951 / 500000000) (3864473 / 1000000) (3865563 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1657 / 16000) (1659 / 16000) (3864473 / 1000000) (3865563 / 1000000) (36543 / 1000) (4573 / 125)
    (7139 / 100) (72051 / 1000) (-142679 / 250) (273959 / 1000000) (357249 / 100) (1181007 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3864473 / 1000000) (108382118043 / 1000000) (1181007 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3864473 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3864473 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell039 :
    ∀ t ∈ Set.Icc ((1659 / 16000) : ℝ) (1661 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1230443901 / 1000000000) : ℝ) ≤ Real.exp (2 * (1659 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1659 / 16000)) (1230443901 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1661 / 16000) : ℝ)) ≤ (19230493 / 15625000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1661 / 16000)) (19230493 / 15625000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((13587083079 / 125000) : ℝ) ≤ Real.exp (3 * (3865439 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3865439 / 1000000)) (13587083079 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1659 / 16000) : ℝ) (1661 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3865439 / 1000000) (386653 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1659 / 16000) (1661 / 16000) (1230443901 / 1000000000) (19230493 / 15625000) (3865439 / 1000000) (386653 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1659 / 16000) (1661 / 16000) (3865439 / 1000000) (386653 / 100000) (36567 / 1000) (4576 / 125)
    (71527 / 1000) (72189 / 1000) (-570791 / 1000) (273371 / 1000000) (1788033 / 500) (2355179 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3865439 / 1000000) (13587083079 / 125000) (2355179 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3865439 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3865439 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityExpCompact_cellsBatch001 :
    ∀ t ∈ Set.Icc ((1621 / 16000) : ℝ) (1661 / 16000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell020
      hpThetaDensityExpCompact_cell021)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell022
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell023
      hpThetaDensityExpCompact_cell024)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell025
      hpThetaDensityExpCompact_cell026)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell027
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell028
      hpThetaDensityExpCompact_cell029))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell030
      hpThetaDensityExpCompact_cell031)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell032
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell033
      hpThetaDensityExpCompact_cell034)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell035
      hpThetaDensityExpCompact_cell036)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell037
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell038
      hpThetaDensityExpCompact_cell039)))))

#print axioms hpThetaDensityExpCompact_cellsBatch001
end HodgeProofHP
