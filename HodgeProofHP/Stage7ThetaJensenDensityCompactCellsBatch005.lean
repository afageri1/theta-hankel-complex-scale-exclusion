/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityCurvatureRationalCells

/-! Exact rational certificates with a full infinite-series remainder bound. -/
noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell100 :
    ∀ t ∈ Set.Icc ((7 / 40) : ℝ) (701 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((354766887 / 250000000) : ℝ) ≤ Real.exp (2 * (7 / 40)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (7 / 40)) (354766887 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((701 / 4000) : ℝ)) ≤ (70988863 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (701 / 4000)) (70988863 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((643057374883 / 1000000) : ℝ) ≤ Real.exp (3 * (2229 / 500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2229 / 500)) (643057374883 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((7 / 40) : ℝ) (701 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2229 / 500) (4460373 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (7 / 40) (701 / 4000) (354766887 / 250000000) (70988863 / 50000000) (2229 / 500) (4460373 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (7 / 40) (701 / 4000) (2229 / 500) (4460373 / 1000000) (13183 / 250) (6604 / 125)
    (894 / 5) (45151 / 250) (-59309 / 125) (71 / 25) (6332931 / 1000) (398099 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2229 / 500) (643057374883 / 1000000) (398099 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2229 / 500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2229 / 500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell101 :
    ∀ t ∈ Set.Icc ((701 / 4000) : ℝ) (351 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1419777259 / 1000000000) : ℝ) ≤ Real.exp (2 * (701 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (701 / 4000)) (1419777259 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((351 / 2000) : ℝ)) ≤ (710243663 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (351 / 2000)) (710243663 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((161843445933 / 250000) : ℝ) ≤ Real.exp (3 * (446023 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (446023 / 100000)) (161843445933 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((701 / 4000) : ℝ) (351 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (446023 / 100000) (4462603 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (701 / 4000) (351 / 2000) (1419777259 / 1000000000) (710243663 / 500000000) (446023 / 100000) (4462603 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (701 / 4000) (351 / 2000) (446023 / 100000) (4462603 / 1000000) (26399 / 500) (26449 / 500)
    (1793 / 10) (90553 / 500) (-473497 / 1000) (711 / 250) (1269121 / 200) (98861 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (446023 / 100000) (161843445933 / 250000) (98861 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (446023 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (446023 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell102 :
    ∀ t ∈ Set.Icc ((351 / 2000) : ℝ) (703 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((56819493 / 40000000) : ℝ) ≤ Real.exp (2 * (351 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (351 / 2000)) (56819493 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((703 / 4000) : ℝ)) ≤ (355299437 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (703 / 4000)) (355299437 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((65171916511 / 100000) : ℝ) ≤ Real.exp (3 * (223123 / 50000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (223123 / 50000)) (65171916511 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((351 / 2000) : ℝ) (703 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (223123 / 50000) (892967 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (351 / 2000) (703 / 4000) (56819493 / 40000000) (355299437 / 250000000) (223123 / 50000) (892967 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (351 / 2000) (703 / 4000) (223123 / 50000) (892967 / 200000) (10573 / 200) (10593 / 200)
    (179801 / 1000) (18161 / 100) (-472501 / 1000) (2849 / 1000) (635831 / 100) (49101 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (223123 / 50000) (65171916511 / 100000) (49101 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (223123 / 50000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (223123 / 50000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell103 :
    ∀ t ∈ Set.Icc ((703 / 4000) : ℝ) (22 / 125), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1421197747 / 1000000000) : ℝ) ≤ Real.exp (2 * (703 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (703 / 4000)) (1421197747 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((22 / 125) : ℝ)) ≤ (355477131 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (22 / 125)) (355477131 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((656097649989 / 1000000) : ℝ) ≤ Real.exp (3 * (1116173 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1116173 / 250000)) (656097649989 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((703 / 4000) : ℝ) (22 / 125),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1116173 / 250000) (1116767 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (703 / 4000) (22 / 125) (1421197747 / 1000000000) (355477131 / 250000000) (1116173 / 250000) (1116767 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (703 / 4000) (22 / 125) (1116173 / 250000) (1116767 / 250000) (52931 / 1000) (53031 / 1000)
    (22538 / 125) (91057 / 500) (-235753 / 500) (2853 / 1000) (6371039 / 1000) (195093 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1116173 / 250000) (656097649989 / 1000000) (195093 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1116173 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1116173 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell104 :
    ∀ t ∈ Set.Icc ((22 / 125) : ℝ) (141 / 800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1421908523 / 1000000000) : ℝ) ≤ Real.exp (2 * (22 / 125)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (22 / 125)) (1421908523 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((141 / 800) : ℝ)) ≤ (177827457 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (141 / 800)) (177827457 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((33025376599 / 50000) : ℝ) ≤ Real.exp (3 * (178677 / 40000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (178677 / 40000)) (33025376599 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((22 / 125) : ℝ) (141 / 800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (178677 / 40000) (2234651 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (22 / 125) (141 / 800) (1421908523 / 1000000000) (177827457 / 125000000) (178677 / 40000) (2234651 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (22 / 125) (141 / 800) (178677 / 40000) (2234651 / 500000) (52997 / 1000) (26549 / 500)
    (180807 / 1000) (9131 / 50) (-94101 / 200) (2857 / 1000) (6383793 / 1000) (387581 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (178677 / 40000) (33025376599 / 50000) (387581 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (178677 / 40000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (178677 / 40000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell105 :
    ∀ t ∈ Set.Icc ((141 / 800) : ℝ) (353 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((284523931 / 200000000) : ℝ) ≤ Real.exp (2 * (141 / 800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (141 / 800)) (284523931 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((353 / 2000) : ℝ)) ≤ (177916393 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (353 / 2000)) (177916393 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((664949048647 / 1000000) : ℝ) ≤ Real.exp (3 * (4469159 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4469159 / 1000000)) (664949048647 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((141 / 800) : ℝ) (353 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4469159 / 1000000) (2235769 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (141 / 800) (353 / 2000) (284523931 / 200000000) (177916393 / 125000000) (4469159 / 1000000) (2235769 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (141 / 800) (353 / 2000) (4469159 / 1000000) (2235769 / 500000) (6633 / 125) (13291 / 250)
    (181311 / 1000) (183127 / 1000) (-46949 / 100) (1431 / 500) (3198289 / 500) (12031 / 31250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4469159 / 1000000) (664949048647 / 1000000) (12031 / 31250000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4469159 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4469159 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell106 :
    ∀ t ∈ Set.Icc ((353 / 2000) : ℝ) (707 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1423331143 / 1000000000) : ℝ) ≤ Real.exp (2 * (353 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (353 / 2000)) (1423331143 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((707 / 4000) : ℝ)) ≤ (1424042987 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (707 / 4000)) (1424042987 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((669422439439 / 1000000) : ℝ) ≤ Real.exp (3 * (2235697 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2235697 / 500000)) (669422439439 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((353 / 2000) : ℝ) (707 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2235697 / 500000) (2236887 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (353 / 2000) (707 / 4000) (1423331143 / 1000000000) (1424042987 / 1000000000) (2235697 / 500000) (2236887 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (353 / 2000) (707 / 4000) (2235697 / 500000) (2236887 / 500000) (5313 / 100) (53231 / 1000)
    (22727 / 125) (91817 / 500) (-117119 / 250) (1433 / 500) (3204691 / 500) (19121 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2235697 / 500000) (669422439439 / 1000000) (19121 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2235697 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2235697 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell107 :
    ∀ t ∈ Set.Icc ((707 / 4000) : ℝ) (177 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((712021493 / 500000000) : ℝ) ≤ Real.exp (2 * (707 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (707 / 4000)) (712021493 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((177 / 1000) : ℝ)) ≤ (1424755187 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (177 / 1000)) (1424755187 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((673929967457 / 1000000) : ℝ) ≤ Real.exp (3 * (4473631 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4473631 / 1000000)) (673929967457 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((707 / 4000) : ℝ) (177 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4473631 / 1000000) (4476011 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (707 / 4000) (177 / 1000) (712021493 / 500000000) (1424755187 / 1000000000) (4473631 / 1000000) (4476011 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (707 / 4000) (177 / 1000) (4473631 / 1000000) (4476011 / 1000000) (53197 / 1000) (53297 / 1000)
    (182323 / 1000) (184143 / 1000) (-467463 / 1000) (287 / 100) (6422211 / 1000) (189931 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4473631 / 1000000) (673929967457 / 1000000) (189931 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4473631 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4473631 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell108 :
    ∀ t ∈ Set.Icc ((177 / 1000) : ℝ) (709 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((712377593 / 500000000) : ℝ) ≤ Real.exp (2 * (177 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (177 / 1000)) (712377593 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((709 / 4000) : ℝ)) ≤ (1425467743 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (709 / 4000)) (1425467743 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((135693569213 / 200000) : ℝ) ≤ Real.exp (3 * (1118967 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1118967 / 250000)) (135693569213 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((177 / 1000) : ℝ) (709 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1118967 / 250000) (17913 / 4000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (177 / 1000) (709 / 4000) (712377593 / 500000000) (1425467743 / 1000000000) (1118967 / 250000) (17913 / 4000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (177 / 1000) (709 / 4000) (1118967 / 250000) (17913 / 4000) (6658 / 125) (13341 / 250)
    (18283 / 100) (184653 / 1000) (-466429 / 1000) (1437 / 500) (6435071 / 1000) (377321 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1118967 / 250000) (135693569213 / 200000) (377321 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1118967 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1118967 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell109 :
    ∀ t ∈ Set.Icc ((709 / 4000) : ℝ) (71 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((712733871 / 500000000) : ℝ) ≤ Real.exp (2 * (709 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (709 / 4000)) (712733871 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((71 / 400) : ℝ)) ≤ (285236131 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (71 / 400)) (285236131 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((170759582173 / 250000) : ℝ) ≤ Real.exp (3 * (2239053 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2239053 / 500000)) (170759582173 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((709 / 4000) : ℝ) (71 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2239053 / 500000) (448049 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (709 / 4000) (71 / 400) (712733871 / 500000000) (285236131 / 200000000) (2239053 / 500000) (448049 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (709 / 4000) (71 / 400) (2239053 / 500000) (448049 / 100000) (5333 / 100) (53431 / 1000)
    (183339 / 1000) (46291 / 250) (-465389 / 1000) (2879 / 1000) (1611989 / 250) (93699 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2239053 / 500000) (170759582173 / 250000) (93699 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2239053 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2239053 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell110 :
    ∀ t ∈ Set.Icc ((71 / 400) : ℝ) (89 / 500), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((713090327 / 500000000) : ℝ) ≤ Real.exp (2 * (71 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (71 / 400)) (713090327 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((89 / 500) : ℝ)) ≤ (1427607549 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (89 / 500)) (1427607549 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((343821862683 / 500000) : ℝ) ≤ Real.exp (3 * (2240173 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2240173 / 500000)) (343821862683 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((71 / 400) : ℝ) (89 / 500),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2240173 / 500000) (1121243 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (71 / 400) (89 / 500) (713090327 / 500000000) (1427607549 / 1000000000) (2240173 / 500000) (1121243 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (71 / 400) (89 / 500) (2240173 / 500000) (1121243 / 250000) (6673 / 125) (26789 / 500)
    (36649 / 200) (186791 / 1000) (-56013 / 125) (2887 / 1000) (1294759 / 200) (186143 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2240173 / 500000) (343821862683 / 500000) (186143 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2240173 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2240173 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell111 :
    ∀ t ∈ Set.Icc ((89 / 500) : ℝ) (357 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((356901887 / 250000000) : ℝ) ≤ Real.exp (2 * (89 / 500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (89 / 500)) (356901887 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((357 / 2000) : ℝ)) ≤ (142903587 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (357 / 2000)) (142903587 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((348477077159 / 500000) : ℝ) ≤ Real.exp (3 * (4484829 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4484829 / 1000000)) (348477077159 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((89 / 500) : ℝ) (357 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4484829 / 1000000) (224473 / 50000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (89 / 500) (357 / 2000) (356901887 / 250000000) (142903587 / 100000000) (4484829 / 1000000) (224473 / 50000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (89 / 500) (357 / 2000) (4484829 / 1000000) (224473 / 50000) (26759 / 500) (53713 / 1000)
    (92133 / 500) (187821 / 1000) (-222971 / 500) (362 / 125) (6499747 / 1000) (367313 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4484829 / 1000000) (348477077159 / 500000) (367313 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4484829 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4484829 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell112 :
    ∀ t ∈ Set.Icc ((357 / 2000) : ℝ) (179 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1429035869 / 1000000000) : ℝ) ≤ Real.exp (2 * (357 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (357 / 2000)) (1429035869 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((179 / 1000) : ℝ)) ≤ (1430465621 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (179 / 1000)) (1430465621 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((706399116577 / 1000000) : ℝ) ≤ Real.exp (3 * (1122329 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1122329 / 250000)) (706399116577 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((357 / 2000) : ℝ) (179 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1122329 / 250000) (4493951 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (357 / 2000) (179 / 1000) (1429035869 / 1000000000) (1430465621 / 1000000000) (1122329 / 250000) (4493951 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (357 / 2000) (179 / 1000) (1122329 / 250000) (4493951 / 1000000) (13413 / 250) (53847 / 1000)
    (185291 / 1000) (37771 / 200) (-443761 / 1000) (581 / 200) (3262897 / 500) (181201 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1122329 / 250000) (706399116577 / 1000000) (181201 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1122329 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1122329 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell113 :
    ∀ t ∈ Set.Icc ((179 / 1000) : ℝ) (359 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((71523281 / 50000000) : ℝ) ≤ Real.exp (2 * (179 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (179 / 1000)) (71523281 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((359 / 2000) : ℝ)) ≤ (715948401 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (359 / 2000)) (715948401 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((71598066339 / 100000) : ℝ) ≤ Real.exp (3 * (4493807 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4493807 / 1000000)) (71598066339 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((179 / 1000) : ℝ) (359 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4493807 / 1000000) (4498447 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (179 / 1000) (359 / 2000) (71523281 / 50000000) (715948401 / 500000000) (4493807 / 1000000) (4498447 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (179 / 1000) (359 / 2000) (4493807 / 1000000) (4498447 / 1000000) (26893 / 500) (26991 / 500)
    (4658 / 25) (94947 / 500) (-220773 / 500) (2913 / 1000) (1637987 / 250) (22347 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4493807 / 1000000) (71598066339 / 100000) (22347 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4493807 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4493807 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell114 :
    ∀ t ∈ Set.Icc ((359 / 2000) : ℝ) (9 / 50), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1431896801 / 1000000000) : ℝ) ≤ Real.exp (2 * (359 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (359 / 2000)) (1431896801 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9 / 50) : ℝ)) ≤ (286665883 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9 / 50)) (286665883 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((45356440989 / 62500) : ℝ) ≤ Real.exp (3 * (4498303 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4498303 / 1000000)) (45356440989 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((359 / 2000) : ℝ) (9 / 50),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4498303 / 1000000) (1125737 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (359 / 2000) (9 / 50) (1431896801 / 1000000000) (286665883 / 200000000) (4498303 / 1000000) (1125737 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (359 / 2000) (9 / 50) (4498303 / 1000000) (1125737 / 250000) (53921 / 1000) (54117 / 1000)
    (187353 / 1000) (23867 / 125) (-87861 / 200) (1461 / 500) (657821 / 100) (176381 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4498303 / 1000000) (45356440989 / 62500) (176381 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4498303 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4498303 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell115 :
    ∀ t ∈ Set.Icc ((9 / 50) : ℝ) (361 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((716664707 / 500000000) : ℝ) ≤ Real.exp (2 * (9 / 50)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9 / 50)) (716664707 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((361 / 2000) : ℝ)) ≤ (1434763461 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (361 / 2000)) (1434763461 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((367784249973 / 500000) : ℝ) ≤ Real.exp (3 * (1125701 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1125701 / 250000)) (367784249973 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9 / 50) : ℝ) (361 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1125701 / 250000) (4507453 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (9 / 50) (361 / 2000) (716664707 / 500000000) (1434763461 / 1000000000) (1125701 / 250000) (4507453 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (9 / 50) (361 / 2000) (1125701 / 250000) (4507453 / 1000000) (6757 / 125) (13563 / 250)
    (188391 / 1000) (191983 / 1000) (-109261 / 250) (2931 / 1000) (3302287 / 500) (348031 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1125701 / 250000) (367784249973 / 500000) (348031 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1125701 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1125701 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell116 :
    ∀ t ∈ Set.Icc ((361 / 2000) : ℝ) (181 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((71738173 / 50000000) : ℝ) ≤ Real.exp (2 * (361 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (361 / 2000)) (71738173 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((181 / 1000) : ℝ)) ≤ (718099471 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (181 / 1000)) (718099471 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((37278850079 / 50000) : ℝ) ≤ Real.exp (3 * (4507309 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4507309 / 1000000)) (37278850079 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((361 / 2000) : ℝ) (181 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4507309 / 1000000) (4511963 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (361 / 2000) (181 / 1000) (71738173 / 50000000) (718099471 / 500000000) (4507309 / 1000000) (4511963 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (361 / 2000) (181 / 1000) (4507309 / 1000000) (4511963 / 1000000) (54191 / 1000) (13597 / 250)
    (189433 / 1000) (96517 / 500) (-434749 / 1000) (147 / 50) (6631047 / 1000) (343359 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4507309 / 1000000) (37278850079 / 50000) (343359 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4507309 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4507309 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell117 :
    ∀ t ∈ Set.Icc ((181 / 1000) : ℝ) (363 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1436198941 / 1000000000) : ℝ) ≤ Real.exp (2 * (181 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (181 / 1000)) (1436198941 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((363 / 2000) : ℝ)) ≤ (71881793 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (363 / 2000)) (71881793 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((377865374461 / 500000) : ℝ) ≤ Real.exp (3 * (2255909 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2255909 / 500000)) (377865374461 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((181 / 1000) : ℝ) (363 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2255909 / 500000) (4516477 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (181 / 1000) (363 / 2000) (1436198941 / 1000000000) (71881793 / 50000000) (2255909 / 500000) (4516477 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (181 / 1000) (363 / 2000) (2255909 / 500000) (4516477 / 1000000) (54327 / 1000) (13631 / 250)
    (95239 / 500) (19409 / 100) (-108107 / 250) (2949 / 1000) (6657623 / 1000) (67749 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2255909 / 500000) (377865374461 / 500000) (67749 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2255909 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2255909 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell118 :
    ∀ t ∈ Set.Icc ((363 / 2000) : ℝ) (91 / 500), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1437635859 / 1000000000) : ℝ) ≤ Real.exp (2 * (363 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (363 / 2000)) (1437635859 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((91 / 500) : ℝ)) ≤ (287814843 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (91 / 500)) (287814843 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((76603656133 / 100000) : ℝ) ≤ Real.exp (3 * (4516333 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4516333 / 1000000)) (76603656133 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((363 / 2000) : ℝ) (91 / 500),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4516333 / 1000000) (1130249 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (363 / 2000) (91 / 500) (1437635859 / 1000000000) (287814843 / 200000000) (4516333 / 1000000) (1130249 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (363 / 2000) (91 / 500) (4516333 / 1000000) (1130249 / 250000) (54463 / 1000) (2733 / 50)
    (191529 / 1000) (195149 / 1000) (-86017 / 200) (1479 / 500) (6684309 / 1000) (83547 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4516333 / 1000000) (76603656133 / 100000) (83547 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4516333 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4516333 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell119 :
    ∀ t ∈ Set.Icc ((91 / 500) : ℝ) (73 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((719537107 / 500000000) : ℝ) ≤ Real.exp (2 * (91 / 500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (91 / 500)) (719537107 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((73 / 400) : ℝ)) ≤ (1440514009 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (73 / 400)) (1440514009 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((388244948783 / 500000) : ℝ) ≤ Real.exp (3 * (4520851 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4520851 / 1000000)) (388244948783 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((91 / 500) : ℝ) (73 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4520851 / 1000000) (4525519 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (91 / 500) (73 / 400) (719537107 / 500000000) (1440514009 / 1000000000) (4520851 / 1000000) (4525519 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (91 / 500) (73 / 400) (4520851 / 1000000) (4525519 / 1000000) (54599 / 1000) (54797 / 1000)
    (192583 / 1000) (196213 / 1000) (-427709 / 1000) (1483 / 500) (3355549 / 500) (329689 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4520851 / 1000000) (388244948783 / 500000) (329689 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4520851 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4520851 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityCompact_cellsBatch005 :
    ∀ t ∈ Set.Icc ((7 / 40) : ℝ) (73 / 400),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell100
      hpThetaDensityCompact_cell101)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell102
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell103
      hpThetaDensityCompact_cell104)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell105
      hpThetaDensityCompact_cell106)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell107
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell108
      hpThetaDensityCompact_cell109))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell110
      hpThetaDensityCompact_cell111)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell112
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell113
      hpThetaDensityCompact_cell114)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell115
      hpThetaDensityCompact_cell116)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell117
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell118
      hpThetaDensityCompact_cell119)))))

#print axioms hpThetaDensityCompact_cellsBatch005
end HodgeProofHP
