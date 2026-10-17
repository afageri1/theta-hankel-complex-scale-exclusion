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
theorem hpThetaDensityCompact_cell040 :
    ∀ t ∈ Set.Icc ((4 / 25) : ℝ) (641 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((344281941 / 250000000) : ℝ) ≤ Real.exp (2 * (4 / 25)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4 / 25)) (344281941 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((641 / 4000) : ℝ)) ≤ (1377816501 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (641 / 4000)) (1377816501 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((216551746209 / 500000) : ℝ) ≤ Real.exp (3 * (2163123 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2163123 / 500000)) (216551746209 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4 / 25) : ℝ) (641 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2163123 / 500000) (4328549 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (4 / 25) (641 / 4000) (344281941 / 250000000) (1377816501 / 1000000000) (2163123 / 500000) (4328549 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (4 / 25) (641 / 4000) (2163123 / 500000) (4328549 / 1000000) (24447 / 500) (12247 / 250)
    (150577 / 1000) (76123 / 500) (-130693 / 250) (649 / 250) (1123361 / 200) (591083 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2163123 / 500000) (216551746209 / 500000) (591083 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2163123 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2163123 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell041 :
    ∀ t ∈ Set.Icc ((641 / 4000) : ℝ) (321 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2755633 / 2000000) : ℝ) ≤ Real.exp (2 * (641 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (641 / 4000)) (2755633 / 2000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((321 / 2000) : ℝ)) ≤ (1378505581 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (321 / 2000)) (1378505581 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((217962160517 / 500000) : ℝ) ≤ Real.exp (3 * (432841 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (432841 / 100000)) (217962160517 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((641 / 4000) : ℝ) (321 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (432841 / 100000) (2165357 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (641 / 4000) (321 / 2000) (2755633 / 2000000) (1378505581 / 1000000000) (432841 / 100000) (2165357 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (641 / 4000) (321 / 2000) (432841 / 100000) (2165357 / 500000) (12239 / 250) (981 / 20)
    (7551 / 50) (15269 / 100) (-522129 / 1000) (13 / 5) (5628051 / 1000) (293629 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (432841 / 100000) (217962160517 / 500000) (293629 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (432841 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (432841 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell042 :
    ∀ t ∈ Set.Icc ((321 / 2000) : ℝ) (643 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((68925279 / 50000000) : ℝ) ≤ Real.exp (2 * (321 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (321 / 2000)) (68925279 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((643 / 4000) : ℝ)) ≤ (1379195007 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (643 / 4000)) (1379195007 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((438764837919 / 1000000) : ℝ) ≤ Real.exp (3 * (173223 / 40000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (173223 / 40000)) (438764837919 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((321 / 2000) : ℝ) (643 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (173223 / 40000) (54161 / 12500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (321 / 2000) (643 / 4000) (68925279 / 50000000) (1379195007 / 1000000000) (173223 / 40000) (54161 / 12500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (321 / 2000) (643 / 4000) (173223 / 40000) (54161 / 12500) (24509 / 500) (6139 / 125)
    (151463 / 1000) (19142 / 125) (-260741 / 500) (651 / 250) (5639319 / 1000) (583457 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (173223 / 40000) (438764837919 / 1000000) (583457 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (173223 / 40000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (173223 / 40000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell043 :
    ∀ t ∈ Set.Icc ((643 / 4000) : ℝ) (161 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((689597503 / 500000000) : ℝ) ≤ Real.exp (2 * (643 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (643 / 4000)) (689597503 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((161 / 1000) : ℝ)) ≤ (172485597 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (161 / 1000)) (172485597 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((88325037691 / 200000) : ℝ) ≤ Real.exp (3 * (4332741 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4332741 / 1000000)) (88325037691 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((643 / 4000) : ℝ) (161 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4332741 / 1000000) (4335047 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (643 / 4000) (161 / 1000) (689597503 / 500000000) (172485597 / 125000000) (4332741 / 1000000) (4335047 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (643 / 4000) (161 / 1000) (4332741 / 1000000) (4335047 / 1000000) (1227 / 25) (1967 / 40)
    (37977 / 250) (76791 / 500) (-520829 / 1000) (2607 / 1000) (5650609 / 1000) (289839 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4332741 / 1000000) (88325037691 / 200000) (289839 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4332741 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4332741 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell044 :
    ∀ t ∈ Set.Icc ((161 / 1000) : ℝ) (129 / 800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((55195391 / 40000000) : ℝ) ≤ Real.exp (2 * (161 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (161 / 1000)) (55195391 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((129 / 800) : ℝ)) ≤ (1380574891 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (129 / 800)) (1380574891 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((444505519153 / 1000000) : ℝ) ≤ Real.exp (3 * (1083727 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1083727 / 250000)) (444505519153 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((161 / 1000) : ℝ) (129 / 800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1083727 / 250000) (867443 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (161 / 1000) (129 / 800) (55195391 / 40000000) (1380574891 / 1000000000) (1083727 / 250000) (867443 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (161 / 1000) (129 / 800) (1083727 / 250000) (867443 / 200000) (24571 / 500) (49237 / 1000)
    (152353 / 1000) (15403 / 100) (-520171 / 1000) (2611 / 1000) (5661921 / 1000) (575921 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1083727 / 250000) (444505519153 / 1000000) (575921 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1083727 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1083727 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell045 :
    ∀ t ∈ Set.Icc ((129 / 800) : ℝ) (323 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((138057489 / 100000000) : ℝ) ≤ Real.exp (2 * (129 / 800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (129 / 800)) (138057489 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((323 / 2000) : ℝ)) ≤ (1381265351 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (323 / 2000)) (1381265351 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((447405977659 / 1000000) : ℝ) ≤ Real.exp (3 * (1084269 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1084269 / 250000)) (447405977659 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((129 / 800) : ℝ) (323 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1084269 / 250000) (542423 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (129 / 800) (323 / 2000) (138057489 / 100000000) (1381265351 / 1000000000) (1084269 / 250000) (542423 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (129 / 800) (323 / 2000) (1084269 / 250000) (542423 / 125000) (12301 / 250) (49299 / 1000)
    (152799 / 1000) (77239 / 500) (-129877 / 250) (523 / 200) (709157 / 125) (143047 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1084269 / 250000) (447405977659 / 1000000) (143047 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1084269 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1084269 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell046 :
    ∀ t ∈ Set.Icc ((323 / 2000) : ℝ) (647 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((27625307 / 20000000) : ℝ) ≤ Real.exp (2 * (323 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (323 / 2000)) (27625307 / 20000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((647 / 4000) : ℝ)) ≤ (1381956157 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (647 / 4000)) (1381956157 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((225163356381 / 500000) : ℝ) ≤ Real.exp (3 * (867849 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (867849 / 200000)) (225163356381 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((323 / 2000) : ℝ) (647 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (867849 / 200000) (2170777 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (323 / 2000) (647 / 4000) (27625307 / 20000000) (1381956157 / 1000000000) (867849 / 200000) (2170777 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (323 / 2000) (647 / 4000) (867849 / 200000) (2170777 / 500000) (24633 / 500) (49361 / 1000)
    (76623 / 500) (154927 / 1000) (-12971 / 25) (2619 / 1000) (1421153 / 250) (568477 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (867849 / 200000) (225163356381 / 500000) (568477 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (867849 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (867849 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell047 :
    ∀ t ∈ Set.Icc ((647 / 4000) : ℝ) (81 / 500), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((345489039 / 250000000) : ℝ) ≤ Real.exp (2 * (647 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (647 / 4000)) (345489039 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((81 / 500) : ℝ)) ≤ (345661827 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (81 / 500)) (345661827 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((56658484301 / 125000) : ℝ) ≤ Real.exp (3 * (868283 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (868283 / 200000)) (56658484301 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((647 / 4000) : ℝ) (81 / 500),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (868283 / 200000) (173749 / 40000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (647 / 4000) (81 / 500) (345489039 / 250000000) (345661827 / 250000000) (868283 / 200000) (173749 / 40000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (647 / 4000) (81 / 500) (868283 / 200000) (173749 / 40000) (49329 / 1000) (6178 / 125)
    (76847 / 500) (155377 / 1000) (-518167 / 1000) (2623 / 1000) (5695991 / 1000) (141197 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (868283 / 200000) (56658484301 / 125000) (141197 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (868283 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (868283 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell048 :
    ∀ t ∈ Set.Icc ((81 / 500) : ℝ) (649 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1382647307 / 1000000000) : ℝ) ≤ Real.exp (2 * (81 / 500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (81 / 500)) (1382647307 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((649 / 4000) : ℝ)) ≤ (345834701 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (649 / 4000)) (345834701 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((57028701713 / 125000) : ℝ) ≤ Real.exp (3 * (2171793 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2171793 / 500000)) (57028701713 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((81 / 500) : ℝ) (649 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2171793 / 500000) (2172949 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (81 / 500) (649 / 4000) (1382647307 / 1000000000) (345834701 / 250000000) (2171793 / 500000) (2172949 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (81 / 500) (649 / 4000) (2171793 / 500000) (2172949 / 500000) (49391 / 1000) (24743 / 500)
    (154143 / 1000) (155829 / 1000) (-258741 / 500) (2627 / 1000) (2853699 / 500) (561121 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2171793 / 500000) (57028701713 / 125000) (561121 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2171793 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2171793 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell049 :
    ∀ t ∈ Set.Icc ((649 / 4000) : ℝ) (13 / 80), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1383338803 / 1000000000) : ℝ) ≤ Real.exp (2 * (649 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (649 / 4000)) (1383338803 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((13 / 80) : ℝ)) ≤ (692015323 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (13 / 80)) (692015323 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((114803020733 / 250000) : ℝ) ≤ Real.exp (3 * (2172879 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2172879 / 500000)) (114803020733 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((649 / 4000) : ℝ) (13 / 80),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2172879 / 500000) (4348071 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (649 / 4000) (13 / 80) (1383338803 / 1000000000) (692015323 / 500000000) (2172879 / 500000) (4348071 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (649 / 4000) (13 / 80) (2172879 / 500000) (4348071 / 1000000) (24727 / 500) (49549 / 1000)
    (154593 / 1000) (156281 / 1000) (-258399 / 500) (2631 / 1000) (5718821 / 1000) (557477 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2172879 / 500000) (114803020733 / 250000) (557477 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2172879 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2172879 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell050 :
    ∀ t ∈ Set.Icc ((13 / 80) : ℝ) (651 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((276806129 / 200000000) : ℝ) ≤ Real.exp (2 * (13 / 80)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (13 / 80)) (276806129 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((651 / 4000) : ℝ)) ≤ (276944567 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (651 / 4000)) (276944567 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((462216822189 / 1000000) : ℝ) ≤ Real.exp (3 * (1086983 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1086983 / 250000)) (462216822189 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((13 / 80) : ℝ) (651 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1086983 / 250000) (2175123 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (13 / 80) (651 / 4000) (276806129 / 200000000) (276944567 / 200000000) (1086983 / 250000) (2175123 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (13 / 80) (651 / 4000) (1086983 / 250000) (2175123 / 500000) (12379 / 250) (49611 / 1000)
    (38761 / 250) (78367 / 500) (-516109 / 1000) (527 / 200) (5730273 / 1000) (553853 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1086983 / 250000) (462216822189 / 1000000) (553853 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1086983 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1086983 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell051 :
    ∀ t ∈ Set.Icc ((651 / 4000) : ℝ) (163 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((692361417 / 500000000) : ℝ) ≤ Real.exp (2 * (651 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (651 / 4000)) (692361417 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((163 / 1000) : ℝ)) ≤ (1385415369 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (163 / 1000)) (1385415369 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((465241221933 / 1000000) : ℝ) ≤ Real.exp (3 * (2175053 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2175053 / 500000)) (465241221933 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((651 / 4000) : ℝ) (163 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2175053 / 500000) (4352421 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (651 / 4000) (163 / 1000) (692361417 / 500000000) (1385415369 / 1000000000) (2175053 / 500000) (4352421 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (651 / 4000) (163 / 1000) (2175053 / 500000) (4352421 / 1000000) (49579 / 1000) (24837 / 500)
    (31099 / 200) (157187 / 1000) (-103083 / 200) (2639 / 1000) (5741741 / 1000) (550253 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2175053 / 500000) (465241221933 / 1000000) (550253 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2175053 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2175053 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell052 :
    ∀ t ∈ Set.Icc ((163 / 1000) : ℝ) (653 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((173176921 / 125000000) : ℝ) ≤ Real.exp (2 * (163 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (163 / 1000)) (173176921 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((653 / 4000) : ℝ)) ≤ (5544433 / 4000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (653 / 4000)) (5544433 / 4000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((29268013781 / 62500) : ℝ) ≤ Real.exp (3 * (2176141 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2176141 / 500000)) (29268013781 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((163 / 1000) : ℝ) (653 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2176141 / 500000) (2177299 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (163 / 1000) (653 / 4000) (173176921 / 125000000) (5544433 / 4000000) (2176141 / 500000) (2177299 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (163 / 1000) (653 / 4000) (2176141 / 500000) (2177299 / 500000) (49641 / 1000) (49737 / 1000)
    (38987 / 250) (78821 / 500) (-102943 / 200) (2643 / 1000) (5753237 / 1000) (34167 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2176141 / 500000) (29268013781 / 62500) (34167 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2176141 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2176141 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell053 :
    ∀ t ∈ Set.Icc ((653 / 4000) : ℝ) (327 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1386108249 / 1000000000) : ℝ) ≤ Real.exp (2 * (653 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (653 / 4000)) (1386108249 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((327 / 2000) : ℝ)) ≤ (693400739 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (327 / 2000)) (693400739 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((235678294251 / 500000) : ℝ) ≤ Real.exp (3 * (4354459 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4354459 / 1000000)) (235678294251 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((653 / 4000) : ℝ) (327 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4354459 / 1000000) (544597 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (653 / 4000) (327 / 2000) (1386108249 / 1000000000) (693400739 / 500000000) (4354459 / 1000000) (544597 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (653 / 4000) (327 / 2000) (4354459 / 1000000) (544597 / 125000) (6213 / 125) (249 / 5)
    (78201 / 500) (79049 / 500) (-51401 / 100) (2647 / 1000) (1441189 / 250) (271557 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4354459 / 1000000) (235678294251 / 500000) (271557 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4354459 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4354459 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell054 :
    ∀ t ∈ Set.Icc ((327 / 2000) : ℝ) (131 / 800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1386801477 / 1000000000) : ℝ) ≤ Real.exp (2 * (327 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (327 / 2000)) (1386801477 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((131 / 800) : ℝ)) ≤ (346873763 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (131 / 800)) (346873763 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((59305632639 / 125000) : ℝ) ≤ Real.exp (3 * (1089159 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1089159 / 250000)) (59305632639 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((327 / 2000) : ℝ) (131 / 800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1089159 / 250000) (871791 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (327 / 2000) (131 / 800) (1386801477 / 1000000000) (346873763 / 250000000) (1089159 / 250000) (871791 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (327 / 2000) (131 / 800) (1089159 / 250000) (871791 / 200000) (49767 / 1000) (49863 / 1000)
    (19607 / 125) (31711 / 200) (-513293 / 1000) (2651 / 1000) (2888149 / 500) (269789 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1089159 / 250000) (59305632639 / 125000) (269789 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1089159 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1089159 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell055 :
    ∀ t ∈ Set.Icc ((131 / 800) : ℝ) (41 / 250), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1387495051 / 1000000000) : ℝ) ≤ Real.exp (2 * (131 / 800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (131 / 800)) (1387495051 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41 / 250) : ℝ)) ≤ (1388188973 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41 / 250)) (1388188973 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((477556635353 / 1000000) : ℝ) ≤ Real.exp (3 * (871763 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (871763 / 200000)) (477556635353 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((131 / 800) : ℝ) (41 / 250),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (871763 / 200000) (872227 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (131 / 800) (41 / 250) (1387495051 / 1000000000) (1388188973 / 1000000000) (871763 / 200000) (872227 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (131 / 800) (41 / 250) (871763 / 200000) (872227 / 200000) (4983 / 100) (24963 / 500)
    (157311 / 1000) (39753 / 250) (-256289 / 500) (531 / 200) (2893931 / 500) (536063 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (871763 / 200000) (477556635353 / 1000000) (536063 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (871763 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (871763 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell056 :
    ∀ t ∈ Set.Icc ((41 / 250) : ℝ) (657 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((347047243 / 250000000) : ℝ) ≤ Real.exp (2 * (41 / 250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41 / 250)) (347047243 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((657 / 4000) : ℝ)) ≤ (1388883241 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (657 / 4000)) (1388883241 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((48069005813 / 100000) : ℝ) ≤ Real.exp (3 * (872199 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (872199 / 200000)) (48069005813 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41 / 250) : ℝ) (657 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (872199 / 200000) (1090829 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41 / 250) (657 / 4000) (347047243 / 250000000) (1388883241 / 1000000000) (872199 / 200000) (1090829 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (41 / 250) (657 / 4000) (872199 / 200000) (1090829 / 250000) (49893 / 1000) (49989 / 1000)
    (19721 / 125) (159471 / 1000) (-511857 / 1000) (2659 / 1000) (724931 / 125) (66571 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (872199 / 200000) (48069005813 / 100000) (66571 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (872199 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (872199 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell057 :
    ∀ t ∈ Set.Icc ((657 / 4000) : ℝ) (329 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((34722081 / 25000000) : ℝ) ≤ Real.exp (2 * (657 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (657 / 4000)) (34722081 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((329 / 2000) : ℝ)) ≤ (10856077 / 7812500) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (329 / 2000)) (10856077 / 7812500) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((96769098331 / 200000) : ℝ) ≤ Real.exp (3 * (545397 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (545397 / 125000)) (96769098331 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((657 / 4000) : ℝ) (329 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (545397 / 125000) (2182749 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (657 / 4000) (329 / 2000) (34722081 / 25000000) (10856077 / 7812500) (545397 / 125000) (2182749 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (657 / 4000) (329 / 2000) (545397 / 125000) (2182749 / 500000) (12489 / 250) (12513 / 250)
    (6329 / 40) (15993 / 100) (-51113 / 100) (2663 / 1000) (2905529 / 500) (105819 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (545397 / 125000) (96769098331 / 200000) (105819 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (545397 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (545397 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell058 :
    ∀ t ∈ Set.Icc ((329 / 2000) : ℝ) (659 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((277915571 / 200000000) : ℝ) ≤ Real.exp (2 * (329 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (329 / 2000)) (277915571 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((659 / 4000) : ℝ)) ≤ (1390272819 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (659 / 4000)) (1390272819 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((487023099403 / 1000000) : ℝ) ≤ Real.exp (3 * (2182679 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2182679 / 500000)) (487023099403 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((329 / 2000) : ℝ) (659 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2182679 / 500000) (2183841 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (329 / 2000) (659 / 4000) (277915571 / 200000000) (1390272819 / 1000000000) (2182679 / 500000) (2183841 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (329 / 2000) (659 / 4000) (2182679 / 500000) (2183841 / 500000) (50019 / 1000) (10023 / 200)
    (158683 / 1000) (160391 / 1000) (-63799 / 125) (2667 / 1000) (1164539 / 200) (525643 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2182679 / 500000) (487023099403 / 1000000) (525643 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2182679 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2182679 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell059 :
    ∀ t ∈ Set.Icc ((659 / 4000) : ℝ) (33 / 200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((695136409 / 500000000) : ℝ) ≤ Real.exp (2 * (659 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (659 / 4000)) (695136409 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((33 / 200) : ℝ)) ≤ (1390968129 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (33 / 200)) (1390968129 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((245112258389 / 500000) : ℝ) ≤ Real.exp (3 * (2183771 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2183771 / 500000)) (245112258389 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((659 / 4000) : ℝ) (33 / 200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2183771 / 500000) (2184933 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (659 / 4000) (33 / 200) (695136409 / 500000000) (1390968129 / 1000000000) (2183771 / 500000) (2184933 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (659 / 4000) (33 / 200) (2183771 / 500000) (2184933 / 500000) (25041 / 500) (25089 / 500)
    (79571 / 500) (40213 / 250) (-509661 / 1000) (2671 / 1000) (116687 / 20) (52221 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2183771 / 500000) (245112258389 / 500000) (52221 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2183771 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2183771 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityCompact_cellsBatch002 :
    ∀ t ∈ Set.Icc ((4 / 25) : ℝ) (33 / 200),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell040
      hpThetaDensityCompact_cell041)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell042
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell043
      hpThetaDensityCompact_cell044)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell045
      hpThetaDensityCompact_cell046)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell047
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell048
      hpThetaDensityCompact_cell049))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell050
      hpThetaDensityCompact_cell051)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell052
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell053
      hpThetaDensityCompact_cell054)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell055
      hpThetaDensityCompact_cell056)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell057
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell058
      hpThetaDensityCompact_cell059)))))

#print axioms hpThetaDensityCompact_cellsBatch002
end HodgeProofHP
