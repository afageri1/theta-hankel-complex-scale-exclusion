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
theorem hpThetaDensityUpperExpCompact_cell120 :
    ∀ t ∈ Set.Icc ((587 / 2000) : ℝ) (589 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1798584559 / 1000000000) : ℝ) ≤ Real.exp (2 * (587 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (587 / 2000)) (1798584559 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((589 / 2000) : ℝ)) ≤ (1802185329 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (589 / 2000)) (1802185329 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((11488973712359 / 500000) : ℝ) ≤ Real.exp (3 * (5650253 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5650253 / 1000000)) (11488973712359 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((587 / 2000) : ℝ) (589 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5650253 / 1000000) (2830873 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (587 / 2000) (589 / 2000) (1798584559 / 1000000000) (1802185329 / 1000000000) (5650253 / 1000000) (2830873 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (587 / 2000) (589 / 2000) (5650253 / 1000000) (2830873 / 500000) (9373 / 100) (2358 / 25)
    (566183 / 1000) (579081 / 1000) (657363 / 500) (4061 / 1000000) (8220373 / 500) (5571 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5650253 / 1000000) (11488973712359 / 500000) (5571 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5650253 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5650253 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell121 :
    ∀ t ∈ Set.Icc ((589 / 2000) : ℝ) (591 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((112636583 / 62500000) : ℝ) ≤ Real.exp (2 * (589 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (589 / 2000)) (112636583 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((591 / 2000) : ℝ)) ≤ (1805793307 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (591 / 2000)) (1805793307 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1188527902183 / 50000) : ℝ) ≤ Real.exp (3 * (1132313 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1132313 / 200000)) (1188527902183 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((589 / 2000) : ℝ) (591 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1132313 / 200000) (5673081 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (589 / 2000) (591 / 2000) (112636583 / 62500000) (1805793307 / 1000000000) (1132313 / 200000) (5673081 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (589 / 2000) (591 / 2000) (1132313 / 200000) (5673081 / 1000000) (47087 / 500) (94767 / 1000)
    (571183 / 1000) (11683 / 20) (134597 / 100) (3949 / 1000000) (8286401 / 500) (1077 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1132313 / 200000) (1188527902183 / 50000) (1077 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1132313 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1132313 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell122 :
    ∀ t ∈ Set.Icc ((591 / 2000) : ℝ) (593 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((902896653 / 500000000) : ℝ) ≤ Real.exp (2 * (591 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (591 / 2000)) (902896653 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((593 / 2000) : ℝ)) ≤ (1809408507 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (593 / 2000)) (1809408507 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2459211495499 / 100000) : ℝ) ≤ Real.exp (3 * (5672899 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5672899 / 1000000)) (2459211495499 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((591 / 2000) : ℝ) (593 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5672899 / 1000000) (2842219 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (591 / 2000) (593 / 2000) (902896653 / 500000000) (1809408507 / 1000000000) (5672899 / 1000000) (2842219 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (591 / 2000) (593 / 2000) (5672899 / 1000000) (2842219 / 500000) (4731 / 50) (47607 / 500)
    (28811 / 50) (73657 / 125) (11021 / 8) (12 / 3125) (1670591 / 100) (1041 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5672899 / 1000000) (2459211495499 / 100000) (1041 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5672899 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5672899 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell123 :
    ∀ t ∈ Set.Icc ((593 / 2000) : ℝ) (119 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((904704253 / 500000000) : ℝ) ≤ Real.exp (2 * (593 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (593 / 2000)) (904704253 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((119 / 400) : ℝ)) ≤ (362606189 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (119 / 400)) (362606189 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((25443803515621 / 1000000) : ℝ) ≤ Real.exp (3 * (177633 / 31250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (177633 / 31250)) (25443803515621 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((593 / 2000) : ℝ) (119 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (177633 / 31250) (5695819 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (593 / 2000) (119 / 400) (904704253 / 500000000) (362606189 / 200000000) (177633 / 31250) (5695819 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (593 / 2000) (119 / 400) (177633 / 31250) (5695819 / 1000000) (23767 / 250) (11958 / 125)
    (290647 / 500) (594401 / 1000) (176214 / 125) (1867 / 500000) (8420051 / 500) (5031 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (177633 / 31250) (25443803515621 / 1000000) (5031 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (177633 / 31250)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (177633 / 31250)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell124 :
    ∀ t ∈ Set.Icc ((119 / 400) : ℝ) (597 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((56657217 / 31250000) : ℝ) ≤ Real.exp (2 * (119 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (119 / 400)) (56657217 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((597 / 2000) : ℝ)) ≤ (454165159 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (597 / 2000)) (454165159 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((5265357007283 / 200000) : ℝ) ≤ Real.exp (3 * (1423909 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1423909 / 250000)) (5265357007283 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((119 / 400) : ℝ) (597 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1423909 / 250000) (2853611 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (119 / 400) (597 / 2000) (56657217 / 31250000) (454165159 / 250000000) (1423909 / 250000) (2853611 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (119 / 400) (597 / 2000) (1423909 / 250000) (2853611 / 500000) (95517 / 1000) (24029 / 250)
    (293203 / 500) (599583 / 1000) (1442207 / 1000) (363 / 100000) (16975363 / 1000) (2431 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1423909 / 250000) (5265357007283 / 200000) (2431 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1423909 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1423909 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell125 :
    ∀ t ∈ Set.Icc ((597 / 2000) : ℝ) (599 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((363332127 / 200000000) : ℝ) ≤ Real.exp (2 * (597 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (597 / 2000)) (363332127 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((599 / 2000) : ℝ)) ≤ (1820297593 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (599 / 2000)) (1820297593 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((13621133769719 / 500000) : ℝ) ≤ Real.exp (3 * (5707039 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5707039 / 1000000)) (13621133769719 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((597 / 2000) : ℝ) (599 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5707039 / 1000000) (5718647 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (597 / 2000) (599 / 2000) (363332127 / 200000000) (1820297593 / 1000000000) (5707039 / 1000000) (5718647 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (597 / 2000) (599 / 2000) (5707039 / 1000000) (5718647 / 1000000) (95969 / 1000) (9657 / 100)
    (591557 / 1000) (604803 / 1000) (295023 / 200) (353 / 100000) (171117 / 10) (4699 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5707039 / 1000000) (13621133769719 / 500000) (4699 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5707039 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5707039 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell126 :
    ∀ t ∈ Set.Icc ((599 / 2000) : ℝ) (601 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((227537199 / 125000000) : ℝ) ≤ Real.exp (2 * (599 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (599 / 2000)) (227537199 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((601 / 2000) : ℝ)) ≤ (1823941831 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (601 / 2000)) (1823941831 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((88098197504 / 3125) : ℝ) ≤ Real.exp (3 * (89351 / 15625)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (89351 / 15625)) (88098197504 / 3125) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((599 / 2000) : ℝ) (601 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (89351 / 15625) (358131 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (599 / 2000) (601 / 2000) (227537199 / 125000000) (1823941831 / 1000000000) (89351 / 15625) (358131 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (599 / 2000) (601 / 2000) (89351 / 15625) (358131 / 62500) (48211 / 500) (48513 / 500)
    (119349 / 200) (610063 / 1000) (1508479 / 1000) (3431 / 1000000) (8624573 / 500) (9081 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (89351 / 15625) (88098197504 / 3125) (9081 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (89351 / 15625)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (89351 / 15625)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell127 :
    ∀ t ∈ Set.Icc ((601 / 2000) : ℝ) (603 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((182394183 / 100000000) : ℝ) ≤ Real.exp (2 * (601 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (601 / 2000)) (182394183 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((603 / 2000) : ℝ)) ≤ (365518673 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (603 / 2000)) (365518673 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((14587862733507 / 500000) : ℝ) ≤ Real.exp (3 * (5729913 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5729913 / 1000000)) (14587862733507 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((601 / 2000) : ℝ) (603 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5729913 / 1000000) (89712 / 15625) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (601 / 2000) (603 / 2000) (182394183 / 100000000) (365518673 / 200000000) (5729913 / 1000000) (89712 / 15625) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (601 / 2000) (603 / 2000) (5729913 / 1000000) (89712 / 15625) (48439 / 500) (97483 / 1000)
    (150493 / 250) (615361 / 1000) (1542267 / 1000) (417 / 125000) (2173462 / 125) (351 / 40000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5729913 / 1000000) (14587862733507 / 500000) (351 / 40000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5729913 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5729913 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell128 :
    ∀ t ∈ Set.Icc ((603 / 2000) : ℝ) (121 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((456898341 / 250000000) : ℝ) ≤ Real.exp (2 * (603 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (603 / 2000)) (456898341 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((121 / 400) : ℝ)) ≤ (1831252209 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (121 / 400)) (1831252209 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3774545294291 / 125000) : ℝ) ≤ Real.exp (3 * (717673 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (717673 / 125000)) (3774545294291 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((603 / 2000) : ℝ) (121 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (717673 / 125000) (2876531 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (603 / 2000) (121 / 400) (456898341 / 250000000) (1831252209 / 1000000000) (717673 / 125000) (2876531 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (603 / 2000) (121 / 400) (717673 / 125000) (2876531 / 500000) (19467 / 200) (97943 / 1000)
    (607237 / 1000) (310349 / 500) (394123 / 250) (1621 / 500000) (4381837 / 250) (4239 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (717673 / 125000) (3774545294291 / 125000) (4239 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (717673 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (717673 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell129 :
    ∀ t ∈ Set.Icc ((121 / 400) : ℝ) (607 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((114453263 / 62500000) : ℝ) ≤ Real.exp (2 * (121 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (121 / 400)) (114453263 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((607 / 2000) : ℝ)) ≤ (1834918379 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (607 / 2000)) (1834918379 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((15627416630619 / 500000) : ℝ) ≤ Real.exp (3 * (2876439 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2876439 / 500000)) (15627416630619 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((121 / 400) : ℝ) (607 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2876439 / 500000) (288229 / 50000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (121 / 400) (607 / 2000) (114453263 / 62500000) (1834918379 / 1000000000) (2876439 / 500000) (288229 / 50000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (121 / 400) (607 / 2000) (2876439 / 500000) (288229 / 50000) (48897 / 500) (19681 / 200)
    (612541 / 1000) (25043 / 40) (201397 / 125) (3151 / 1000000) (8834067 / 500) (8191 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2876439 / 500000) (15627416630619 / 500000) (8191 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2876439 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2876439 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell130 :
    ∀ t ∈ Set.Icc ((607 / 2000) : ℝ) (609 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((917459189 / 500000000) : ℝ) ≤ Real.exp (2 * (607 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (607 / 2000)) (917459189 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((609 / 2000) : ℝ)) ≤ (114911993 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (609 / 2000)) (114911993 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8088176843863 / 250000) : ℝ) ≤ Real.exp (3 * (1441099 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1441099 / 250000)) (8088176843863 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((607 / 2000) : ℝ) (609 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1441099 / 250000) (5776121 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (607 / 2000) (609 / 2000) (917459189 / 500000000) (114911993 / 62500000) (1441099 / 250000) (5776121 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (607 / 2000) (609 / 2000) (1441099 / 250000) (5776121 / 1000000) (12282 / 125) (24717 / 250)
    (123577 / 200) (631491 / 1000) (823149 / 500) (3063 / 1000000) (17810049 / 1000) (7913 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1441099 / 250000) (8088176843863 / 250000) (7913 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1441099 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1441099 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell131 :
    ∀ t ∈ Set.Icc ((609 / 2000) : ℝ) (611 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1838591887 / 1000000000) : ℝ) ≤ Real.exp (2 * (609 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (609 / 2000)) (1838591887 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((611 / 2000) : ℝ)) ≤ (1842272751 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (611 / 2000)) (1842272751 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8372831528631 / 250000) : ℝ) ≤ Real.exp (3 * (90249 / 15625)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (90249 / 15625)) (8372831528631 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((609 / 2000) : ℝ) (611 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (90249 / 15625) (1157537 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (609 / 2000) (611 / 2000) (1838591887 / 1000000000) (1842272751 / 1000000000) (90249 / 15625) (1157537 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (609 / 2000) (611 / 2000) (90249 / 15625) (1157537 / 200000) (98719 / 1000) (49667 / 500)
    (155817 / 250) (636947 / 1000) (840943 / 500) (93 / 31250) (2244138 / 125) (1911 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (90249 / 15625) (8372831528631 / 250000) (1911 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (90249 / 15625)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (90249 / 15625)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell132 :
    ∀ t ∈ Set.Icc ((611 / 2000) : ℝ) (613 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((7369091 / 4000000) : ℝ) ≤ Real.exp (2 * (611 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (611 / 2000)) (7369091 / 4000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((613 / 2000) : ℝ)) ≤ (230745123 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (613 / 2000)) (230745123 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((34672377365539 / 1000000) : ℝ) ≤ Real.exp (3 * (5787499 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5787499 / 1000000)) (34672377365539 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((611 / 2000) : ℝ) (613 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5787499 / 1000000) (724909 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (611 / 2000) (613 / 2000) (7369091 / 4000000) (230745123 / 125000000) (5787499 / 1000000) (724909 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (611 / 2000) (613 / 2000) (5787499 / 1000000) (724909 / 125000) (12398 / 125) (49901 / 500)
    (62869 / 100) (160611 / 250) (429483 / 250) (723 / 250000) (3619461 / 200) (923 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5787499 / 1000000) (34672377365539 / 1000000) (923 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5787499 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5787499 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell133 :
    ∀ t ∈ Set.Icc ((613 / 2000) : ℝ) (123 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1845960983 / 1000000000) : ℝ) ≤ Real.exp (2 * (613 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (613 / 2000)) (1845960983 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((123 / 400) : ℝ)) ≤ (9248283 / 5000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (123 / 400)) (9248283 / 5000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1794881389627 / 50000) : ℝ) ≤ Real.exp (3 * (2899543 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2899543 / 500000)) (1794881389627 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((613 / 2000) : ℝ) (123 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2899543 / 500000) (2905441 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (613 / 2000) (123 / 400) (1845960983 / 1000000000) (9248283 / 5000000) (2899543 / 500000) (2905441 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (613 / 2000) (123 / 400) (2899543 / 500000) (2905441 / 500000) (24913 / 250) (100271 / 1000)
    (634153 / 1000) (32399 / 50) (175443 / 100) (281 / 100000) (9121331 / 500) (1783 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2899543 / 500000) (1794881389627 / 50000) (1783 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2899543 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2899543 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell134 :
    ∀ t ∈ Set.Icc ((123 / 400) : ℝ) (617 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1849656599 / 1000000000) : ℝ) ≤ Real.exp (2 * (123 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (123 / 400)) (1849656599 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((617 / 2000) : ℝ)) ≤ (370671923 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (617 / 2000)) (370671923 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((18584352051981 / 500000) : ℝ) ≤ Real.exp (3 * (726337 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (726337 / 125000)) (18584352051981 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((123 / 400) : ℝ) (617 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (726337 / 125000) (1164503 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (123 / 400) (617 / 2000) (1849656599 / 1000000000) (370671923 / 200000000) (726337 / 125000) (1164503 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (123 / 400) (617 / 2000) (726337 / 125000) (1164503 / 200000) (100121 / 1000) (100743 / 1000)
    (639657 / 1000) (653557 / 1000) (447849 / 250) (2731 / 1000000) (2298648 / 125) (861 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (726337 / 125000) (18584352051981 / 500000) (861 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (726337 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (726337 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell135 :
    ∀ t ∈ Set.Icc ((617 / 2000) : ℝ) (619 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((926679807 / 500000000) : ℝ) ≤ Real.exp (2 * (617 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (617 / 2000)) (926679807 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((619 / 2000) : ℝ)) ≤ (1857070043 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (619 / 2000)) (1857070043 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((19243701938537 / 500000) : ℝ) ≤ Real.exp (3 * (5822329 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5822329 / 1000000)) (19243701938537 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((617 / 2000) : ℝ) (619 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5822329 / 1000000) (1458543 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (617 / 2000) (619 / 2000) (926679807 / 500000000) (1857070043 / 1000000000) (5822329 / 1000000) (1458543 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (617 / 2000) (619 / 2000) (5822329 / 1000000) (1458543 / 250000) (100593 / 1000) (101217 / 1000)
    (645201 / 1000) (82397 / 125) (36577 / 20) (2653 / 1000000) (4634223 / 250) (1663 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (5822329 / 1000000) (19243701938537 / 500000) (1663 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5822329 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5822329 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell136 :
    ∀ t ∈ Set.Icc ((619 / 2000) : ℝ) (621 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((928535021 / 500000000) : ℝ) ≤ Real.exp (2 * (619 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (619 / 2000)) (928535021 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((621 / 2000) : ℝ)) ≤ (18607879 / 10000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (621 / 2000)) (18607879 / 10000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((9963899539567 / 250000) : ℝ) ≤ Real.exp (3 * (1166797 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1166797 / 200000)) (9963899539567 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((619 / 2000) : ℝ) (621 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1166797 / 200000) (1461463 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (619 / 2000) (621 / 2000) (928535021 / 500000000) (18607879 / 10000000) (1166797 / 200000) (1461463 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (619 / 2000) (621 / 2000) (1166797 / 200000) (1461463 / 250000) (50533 / 500) (101693 / 1000)
    (130157 / 200) (132967 / 200) (1866781 / 1000) (2577 / 1000000) (18685781 / 1000) (803 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1166797 / 200000) (9963899539567 / 250000) (803 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1166797 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1166797 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell137 :
    ∀ t ∈ Set.Icc ((621 / 2000) : ℝ) (623 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1860787899 / 1000000000) : ℝ) ≤ Real.exp (2 * (621 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (621 / 2000)) (1860787899 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((623 / 2000) : ℝ)) ≤ (4661283 / 2500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (623 / 2000)) (4661283 / 2500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((41275358268157 / 1000000) : ℝ) ≤ Real.exp (3 * (1169133 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1169133 / 200000)) (41275358268157 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((621 / 2000) : ℝ) (623 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1169133 / 200000) (1171511 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (621 / 2000) (623 / 2000) (1860787899 / 1000000000) (4661283 / 2500000) (1169133 / 200000) (1171511 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (621 / 2000) (623 / 2000) (1169133 / 200000) (1171511 / 200000) (101541 / 1000) (10217 / 100)
    (656411 / 1000) (83817 / 125) (238148 / 125) (313 / 125000) (9417931 / 500) (6203 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1169133 / 200000) (41275358268157 / 1000000) (6203 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1169133 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1169133 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell138 :
    ∀ t ∈ Set.Icc ((623 / 2000) : ℝ) (5 / 16), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1864513199 / 1000000000) : ℝ) ≤ Real.exp (2 * (623 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (623 / 2000)) (1864513199 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((5 / 16) : ℝ)) ≤ (934122979 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (5 / 16)) (934122979 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((42748596794249 / 1000000) : ℝ) ≤ Real.exp (3 * (732171 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (732171 / 125000)) (42748596794249 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((623 / 2000) : ℝ) (5 / 16),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (732171 / 125000) (2934641 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (623 / 2000) (5 / 16) (1864513199 / 1000000000) (934122979 / 500000000) (732171 / 125000) (2934641 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (623 / 2000) (5 / 16) (732171 / 125000) (2934641 / 500000) (102019 / 1000) (2053 / 20)
    (331039 / 500) (676279 / 1000) (194409 / 100) (38 / 15625) (3797431 / 200) (5989 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (732171 / 125000) (42748596794249 / 1000000) (5989 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (732171 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (732171 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell139 :
    ∀ t ∈ Set.Icc ((5 / 16) : ℝ) (627 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1868245957 / 1000000000) : ℝ) ≤ Real.exp (2 * (5 / 16)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (5 / 16)) (1868245957 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((627 / 2000) : ℝ)) ≤ (1871986189 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (627 / 2000)) (1871986189 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((22138712457119 / 500000) : ℝ) ≤ Real.exp (3 * (2934547 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2934547 / 500000)) (22138712457119 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((5 / 16) : ℝ) (627 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2934547 / 500000) (735129 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (5 / 16) (627 / 2000) (1868245957 / 1000000000) (1871986189 / 1000000000) (2934547 / 500000) (735129 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (5 / 16) (627 / 2000) (2934547 / 500000) (735129 / 125000) (51249 / 500) (25783 / 250)
    (667787 / 1000) (85258 / 125) (1983489 / 1000) (1181 / 500000) (9569829 / 500) (2891 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2934547 / 500000) (22138712457119 / 500000) (2891 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2934547 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2934547 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityUpperExpCompact_cellsBatch006 :
    ∀ t ∈ Set.Icc ((587 / 2000) : ℝ) (627 / 2000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell120
      hpThetaDensityUpperExpCompact_cell121)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell122
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell123
      hpThetaDensityUpperExpCompact_cell124)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell125
      hpThetaDensityUpperExpCompact_cell126)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell127
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell128
      hpThetaDensityUpperExpCompact_cell129))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell130
      hpThetaDensityUpperExpCompact_cell131)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell132
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell133
      hpThetaDensityUpperExpCompact_cell134)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell135
      hpThetaDensityUpperExpCompact_cell136)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell137
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell138
      hpThetaDensityUpperExpCompact_cell139)))))

#print axioms hpThetaDensityUpperExpCompact_cellsBatch006
end HodgeProofHP
