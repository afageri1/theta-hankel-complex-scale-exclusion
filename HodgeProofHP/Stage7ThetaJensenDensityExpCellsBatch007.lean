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
theorem hpThetaDensityExpCompact_cell140 :
    ∀ t ∈ Set.Icc ((1861 / 16000) : ℝ) (1863 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((50476327 / 40000000) : ℝ) ≤ Real.exp (2 * (1861 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1861 / 16000)) (50476327 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1863 / 16000) : ℝ)) ≤ (315555923 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1863 / 16000)) (315555923 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((146217565549 / 1000000) : ℝ) ≤ Real.exp (3 * (991071 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (991071 / 250000)) (146217565549 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1861 / 16000) : ℝ) (1863 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (991071 / 250000) (1982701 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1861 / 16000) (1863 / 16000) (50476327 / 40000000) (315555923 / 250000000) (991071 / 250000) (1982701 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1861 / 16000) (1863 / 16000) (991071 / 250000) (1982701 / 500000) (39069 / 1000) (4889 / 125)
    (86139 / 1000) (21711 / 250) (-575717 / 1000) (219213 / 1000000) (791223 / 200) (54713 / 31250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (991071 / 250000) (146217565549 / 1000000) (54713 / 31250000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (991071 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (991071 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell141 :
    ∀ t ∈ Set.Icc ((1863 / 16000) : ℝ) (373 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1262223691 / 1000000000) : ℝ) ≤ Real.exp (2 * (1863 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1863 / 16000)) (1262223691 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((373 / 3200) : ℝ)) ≤ (1262539287 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (373 / 3200)) (1262539287 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((146652916417 / 1000000) : ℝ) ≤ Real.exp (3 * (158611 / 40000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (158611 / 40000)) (146652916417 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1863 / 16000) : ℝ) (373 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (158611 / 40000) (1983197 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1863 / 16000) (373 / 3200) (1262223691 / 1000000000) (1262539287 / 1000000000) (158611 / 40000) (1983197 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1863 / 16000) (373 / 3200) (158611 / 40000) (1983197 / 500000) (7819 / 200) (19569 / 500)
    (86291 / 1000) (43499 / 500) (-57573 / 100) (218727 / 1000000) (158403 / 40) (1745619 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (158611 / 40000) (146652916417 / 1000000) (1745619 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (158611 / 40000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (158611 / 40000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell142 :
    ∀ t ∈ Set.Icc ((373 / 3200) : ℝ) (1867 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((631269643 / 500000000) : ℝ) ≤ Real.exp (2 * (373 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (373 / 3200)) (631269643 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1867 / 16000) : ℝ)) ≤ (631427481 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1867 / 16000)) (631427481 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((147090004771 / 1000000) : ℝ) ≤ Real.exp (3 * (3966267 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3966267 / 1000000)) (147090004771 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((373 / 3200) : ℝ) (1867 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3966267 / 1000000) (1983693 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (373 / 3200) (1867 / 16000) (631269643 / 500000000) (631427481 / 500000000) (3966267 / 1000000) (1983693 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (373 / 3200) (1867 / 16000) (3966267 / 1000000) (1983693 / 500000) (978 / 25) (9791 / 250)
    (21611 / 250) (87151 / 1000) (-143937 / 250) (682 / 3125) (1982019 / 500) (1740431 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3966267 / 1000000) (147090004771 / 1000000) (1740431 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3966267 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3966267 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell143 :
    ∀ t ∈ Set.Icc ((1867 / 16000) : ℝ) (1869 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1262854961 / 1000000000) : ℝ) ≤ Real.exp (2 * (1867 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1867 / 16000)) (1262854961 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1869 / 16000) : ℝ)) ≤ (252634143 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1869 / 16000)) (252634143 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4610248539 / 31250) : ℝ) ≤ Real.exp (3 * (1983629 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1983629 / 500000)) (4610248539 / 31250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1867 / 16000) : ℝ) (1869 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1983629 / 500000) (1984189 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1867 / 16000) (1869 / 16000) (1262854961 / 1000000000) (252634143 / 200000000) (1983629 / 500000) (1984189 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1867 / 16000) (1869 / 16000) (1983629 / 500000) (1984189 / 500000) (19573 / 500) (39189 / 1000)
    (86597 / 1000) (17461 / 200) (-575759 / 1000) (54439 / 250000) (793601 / 200) (347053 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1983629 / 500000) (4610248539 / 31250) (347053 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1983629 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1983629 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell144 :
    ∀ t ∈ Set.Icc ((1869 / 16000) : ℝ) (1871 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((631585357 / 500000000) : ℝ) ≤ Real.exp (2 * (1869 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1869 / 16000)) (631585357 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1871 / 16000) : ℝ)) ≤ (1263486547 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1871 / 16000)) (1263486547 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((147967649579 / 1000000) : ℝ) ≤ Real.exp (3 * (15873 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (15873 / 4000)) (147967649579 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1869 / 16000) : ℝ) (1871 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (15873 / 4000) (396937 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1869 / 16000) (1871 / 16000) (631585357 / 500000000) (1263486547 / 1000000000) (15873 / 4000) (396937 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1869 / 16000) (1871 / 16000) (15873 / 4000) (396937 / 100000) (39171 / 1000) (7843 / 200)
    (86751 / 1000) (87459 / 1000) (-71972 / 125) (217271 / 1000000) (1985987 / 500) (432527 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (15873 / 4000) (147967649579 / 1000000) (432527 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (15873 / 4000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (15873 / 4000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell145 :
    ∀ t ∈ Set.Icc ((1871 / 16000) : ℝ) (1873 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((631743273 / 500000000) : ℝ) ≤ Real.exp (2 * (1871 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1871 / 16000)) (631743273 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1873 / 16000) : ℝ)) ≤ (631901229 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1873 / 16000)) (631901229 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((37102164097 / 250000) : ℝ) ≤ Real.exp (3 * (1984621 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1984621 / 500000)) (37102164097 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1871 / 16000) : ℝ) (1873 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1984621 / 500000) (1985181 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1871 / 16000) (1873 / 16000) (631743273 / 500000000) (631901229 / 500000000) (1984621 / 500000) (1985181 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1871 / 16000) (1873 / 16000) (1984621 / 500000) (1985181 / 500000) (39197 / 1000) (981 / 25)
    (10863 / 125) (87613 / 1000) (-575791 / 1000) (54197 / 250000) (1987973 / 500) (1724967 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1984621 / 500000) (37102164097 / 250000) (1724967 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1984621 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1984621 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell146 :
    ∀ t ∈ Set.Icc ((1873 / 16000) : ℝ) (15 / 128), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1263802457 / 1000000000) : ℝ) ≤ Real.exp (2 * (1873 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1873 / 16000)) (1263802457 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((15 / 128) : ℝ)) ≤ (79007403 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (15 / 128)) (79007403 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((29770284827 / 200000) : ℝ) ≤ Real.exp (3 * (794047 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (794047 / 200000)) (29770284827 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1873 / 16000) : ℝ) (15 / 128),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (794047 / 200000) (794271 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1873 / 16000) (15 / 128) (1263802457 / 1000000000) (79007403 / 62500000) (794047 / 200000) (794271 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1873 / 16000) (15 / 128) (794047 / 200000) (794271 / 200000) (19611 / 500) (19633 / 500)
    (43529 / 500) (87767 / 1000) (-287903 / 500) (108153 / 500000) (159197 / 40) (429959 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (794047 / 200000) (29770284827 / 200000) (429959 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (794047 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (794047 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell147 :
    ∀ t ∈ Set.Icc ((15 / 128) : ℝ) (1877 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1264118447 / 1000000000) : ℝ) ≤ Real.exp (2 * (15 / 128)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (15 / 128)) (1264118447 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1877 / 16000) : ℝ)) ≤ (1264434517 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1877 / 16000)) (1264434517 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((149295512847 / 1000000) : ℝ) ≤ Real.exp (3 * (992807 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (992807 / 250000)) (149295512847 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((15 / 128) : ℝ) (1877 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (992807 / 250000) (993087 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (15 / 128) (1877 / 16000) (1264118447 / 1000000000) (1264434517 / 1000000000) (992807 / 250000) (993087 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (15 / 128) (1877 / 16000) (992807 / 250000) (993087 / 250000) (4906 / 125) (39291 / 1000)
    (21803 / 250) (87921 / 1000) (-28791 / 50) (13489 / 62500) (3983907 / 1000) (10717 / 6250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (992807 / 250000) (149295512847 / 1000000) (10717 / 6250000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (992807 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (992807 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell148 :
    ∀ t ∈ Set.Icc ((1877 / 16000) : ℝ) (1879 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((316108629 / 250000000) : ℝ) ≤ Real.exp (2 * (1877 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1877 / 16000)) (316108629 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1879 / 16000) : ℝ)) ≤ (632375333 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1879 / 16000)) (632375333 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((74870463233 / 500000) : ℝ) ≤ Real.exp (3 * (3972221 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3972221 / 1000000)) (74870463233 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1877 / 16000) : ℝ) (1879 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3972221 / 1000000) (3973341 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1877 / 16000) (1879 / 16000) (316108629 / 250000000) (632375333 / 500000000) (3972221 / 1000000) (3973341 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1877 / 16000) (1879 / 16000) (3972221 / 1000000) (3973341 / 1000000) (19637 / 500) (39317 / 1000)
    (43683 / 500) (3523 / 40) (-287917 / 500) (13459 / 62500) (996973 / 250) (85481 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3972221 / 1000000) (74870463233 / 500000) (85481 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3972221 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3972221 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell149 :
    ∀ t ∈ Set.Icc ((1879 / 16000) : ℝ) (1881 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((252950133 / 200000000) : ℝ) ≤ Real.exp (2 * (1879 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1879 / 16000)) (252950133 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1881 / 16000) : ℝ)) ≤ (1265066893 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1881 / 16000)) (1265066893 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((9386729309 / 62500) : ℝ) ≤ Real.exp (3 * (1986607 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1986607 / 500000)) (9386729309 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1879 / 16000) : ℝ) (1881 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1986607 / 500000) (794867 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1879 / 16000) (1881 / 16000) (252950133 / 200000000) (1265066893 / 1000000000) (1986607 / 500000) (794867 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1879 / 16000) (1881 / 16000) (1986607 / 500000) (794867 / 200000) (39299 / 1000) (39343 / 1000)
    (2188 / 25) (8823 / 100) (-575841 / 1000) (13429 / 62500) (997971 / 250) (340907 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1986607 / 500000) (9386729309 / 62500) (340907 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1986607 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1986607 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell150 :
    ∀ t ∈ Set.Icc ((1881 / 16000) : ℝ) (1883 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((316266723 / 250000000) : ℝ) ≤ Real.exp (2 * (1881 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1881 / 16000)) (316266723 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1883 / 16000) : ℝ)) ≤ (1265383199 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1883 / 16000)) (1265383199 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((30127148849 / 200000) : ℝ) ≤ Real.exp (3 * (3974207 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3974207 / 1000000)) (30127148849 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1881 / 16000) : ℝ) (1883 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3974207 / 1000000) (124229 / 31250) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1881 / 16000) (1883 / 16000) (316266723 / 250000000) (1265383199 / 1000000000) (3974207 / 1000000) (124229 / 31250) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1881 / 16000) (1883 / 16000) (3974207 / 1000000) (124229 / 31250) (1573 / 40) (4921 / 125)
    (3507 / 40) (17677 / 200) (-575853 / 1000) (107193 / 500000) (31967 / 8) (212433 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3974207 / 1000000) (30127148849 / 200000) (212433 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3974207 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3974207 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell151 :
    ∀ t ∈ Set.Icc ((1883 / 16000) : ℝ) (377 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((632691599 / 500000000) : ℝ) ≤ Real.exp (2 * (1883 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1883 / 16000)) (632691599 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((377 / 3200) : ℝ)) ≤ (4944139 / 3906250) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (377 / 3200)) (4944139 / 3906250) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((75542804801 / 500000) : ℝ) ≤ Real.exp (3 * (3975201 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3975201 / 1000000)) (75542804801 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1883 / 16000) : ℝ) (377 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3975201 / 1000000) (1988161 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1883 / 16000) (377 / 3200) (632691599 / 500000000) (4944139 / 3906250) (3975201 / 1000000) (1988161 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1883 / 16000) (377 / 3200) (3975201 / 1000000) (1988161 / 500000) (787 / 20) (19697 / 500)
    (8783 / 100) (4427 / 50) (-115173 / 200) (53477 / 250000) (3999873 / 1000) (423601 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3975201 / 1000000) (75542804801 / 500000) (423601 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3975201 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3975201 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell152 :
    ∀ t ∈ Set.Icc ((377 / 3200) : ℝ) (1887 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1265699583 / 1000000000) : ℝ) ≤ Real.exp (2 * (377 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (377 / 3200)) (1265699583 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1887 / 16000) : ℝ)) ≤ (1266016049 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1887 / 16000)) (1266016049 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((151536818453 / 1000000) : ℝ) ≤ Real.exp (3 * (795239 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (795239 / 200000)) (151536818453 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((377 / 3200) : ℝ) (1887 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (795239 / 200000) (3977317 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (377 / 3200) (1887 / 16000) (1265699583 / 1000000000) (1266016049 / 1000000000) (795239 / 200000) (3977317 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (377 / 3200) (1887 / 16000) (795239 / 200000) (3977317 / 1000000) (4922 / 125) (1971 / 50)
    (10998 / 125) (17739 / 200) (-57587 / 100) (213431 / 1000000) (2001939 / 500) (1689359 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (795239 / 200000) (151536818453 / 1000000) (1689359 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (795239 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (795239 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell153 :
    ∀ t ∈ Set.Icc ((1887 / 16000) : ℝ) (1889 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((79126003 / 62500000) : ℝ) ≤ Real.exp (2 * (1887 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1887 / 16000)) (79126003 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1889 / 16000) : ℝ)) ≤ (79145787 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1889 / 16000)) (79145787 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((15198937481 / 100000) : ℝ) ≤ Real.exp (3 * (3977189 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3977189 / 1000000)) (15198937481 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1887 / 16000) : ℝ) (1889 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3977189 / 1000000) (3978311 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1887 / 16000) (1889 / 16000) (79126003 / 62500000) (79145787 / 62500000) (3977189 / 1000000) (3978311 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1887 / 16000) (1889 / 16000) (3977189 / 1000000) (3978311 / 1000000) (19701 / 500) (7889 / 200)
    (88139 / 1000) (88851 / 1000) (-14397 / 25) (42591 / 200000) (2003941 / 500) (1684329 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3977189 / 1000000) (15198937481 / 100000) (1684329 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3977189 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3977189 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell154 :
    ∀ t ∈ Set.Icc ((1889 / 16000) : ℝ) (1891 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1266332591 / 1000000000) : ℝ) ≤ Real.exp (2 * (1889 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1889 / 16000)) (1266332591 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1891 / 16000) : ℝ)) ≤ (253329843 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1891 / 16000)) (253329843 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((152443282697 / 1000000) : ℝ) ≤ Real.exp (3 * (3978183 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3978183 / 1000000)) (152443282697 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1889 / 16000) : ℝ) (1891 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3978183 / 1000000) (1989653 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1889 / 16000) (1891 / 16000) (1266332591 / 1000000000) (253329843 / 200000000) (3978183 / 1000000) (1989653 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1889 / 16000) (1891 / 16000) (3978183 / 1000000) (1989653 / 500000) (39427 / 1000) (39471 / 1000)
    (44147 / 500) (44503 / 500) (-143971 / 250) (664 / 3125) (4011893 / 1000) (839657 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3978183 / 1000000) (152443282697 / 1000000) (839657 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3978183 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3978183 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell155 :
    ∀ t ∈ Set.Icc ((1891 / 16000) : ℝ) (1893 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((633324607 / 500000000) : ℝ) ≤ Real.exp (2 * (1891 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1891 / 16000)) (633324607 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1893 / 16000) : ℝ)) ≤ (1266965917 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1893 / 16000)) (1266965917 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((152899004847 / 1000000) : ℝ) ≤ Real.exp (3 * (1989589 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1989589 / 500000)) (152899004847 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1891 / 16000) : ℝ) (1893 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1989589 / 500000) (3980301 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1891 / 16000) (1893 / 16000) (633324607 / 500000000) (1266965917 / 1000000000) (1989589 / 500000) (3980301 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1891 / 16000) (1893 / 16000) (1989589 / 500000) (3980301 / 1000000) (39453 / 1000) (39497 / 1000)
    (88449 / 1000) (44581 / 500) (-575893 / 1000) (106003 / 500000) (4015907 / 1000) (418577 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1989589 / 500000) (152899004847 / 1000000) (418577 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1989589 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1989589 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell156 :
    ∀ t ∈ Set.Icc ((1893 / 16000) : ℝ) (379 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((316741479 / 250000000) : ℝ) ≤ Real.exp (2 * (1893 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1893 / 16000)) (316741479 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((379 / 3200) : ℝ)) ≤ (633641349 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (379 / 3200)) (633641349 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((19169511169 / 125000) : ℝ) ≤ Real.exp (3 * (3980173 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3980173 / 1000000)) (19169511169 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1893 / 16000) : ℝ) (379 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3980173 / 1000000) (248831 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1893 / 16000) (379 / 3200) (316741479 / 250000000) (633641349 / 500000000) (3980173 / 1000000) (248831 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1893 / 16000) (379 / 3200) (3980173 / 1000000) (248831 / 62500) (39479 / 1000) (19761 / 500)
    (17721 / 200) (44659 / 500) (-575901 / 1000) (211533 / 1000000) (160797 / 40) (834659 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3980173 / 1000000) (19169511169 / 125000) (834659 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3980173 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3980173 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell157 :
    ∀ t ∈ Set.Icc ((379 / 3200) : ℝ) (1897 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1267282697 / 1000000000) : ℝ) ≤ Real.exp (2 * (379 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (379 / 3200)) (1267282697 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1897 / 16000) : ℝ)) ≤ (633799779 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1897 / 16000)) (633799779 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((153814540287 / 1000000) : ℝ) ≤ Real.exp (3 * (248823 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (248823 / 62500)) (153814540287 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((379 / 3200) : ℝ) (1897 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (248823 / 62500) (3982291 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (379 / 3200) (1897 / 16000) (1267282697 / 1000000000) (633799779 / 500000000) (248823 / 62500) (3982291 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (379 / 3200) (1897 / 16000) (248823 / 62500) (3982291 / 1000000) (7901 / 200) (9887 / 250)
    (2219 / 25) (44737 / 500) (-143977 / 250) (10553 / 50000) (804789 / 200) (1664343 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (248823 / 62500) (153814540287 / 1000000) (1664343 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (248823 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (248823 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell158 :
    ∀ t ∈ Set.Icc ((1897 / 16000) : ℝ) (1899 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1267599557 / 1000000000) : ℝ) ≤ Real.exp (2 * (1897 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1897 / 16000)) (1267599557 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1899 / 16000) : ℝ)) ≤ (633958249 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1899 / 16000)) (633958249 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((77137412279 / 500000) : ℝ) ≤ Real.exp (3 * (995541 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (995541 / 250000)) (77137412279 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1897 / 16000) : ℝ) (1899 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (995541 / 250000) (3983287 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1897 / 16000) (1899 / 16000) (1267599557 / 1000000000) (633958249 / 500000000) (995541 / 250000) (3983287 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1897 / 16000) (1899 / 16000) (995541 / 250000) (3983287 / 1000000) (3953 / 100) (19787 / 500)
    (22229 / 250) (8963 / 100) (-115183 / 200) (52647 / 250000) (1006993 / 250) (1659377 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (995541 / 250000) (77137412279 / 500000) (1659377 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (995541 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (995541 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell159 :
    ∀ t ∈ Set.Icc ((1899 / 16000) : ℝ) (1901 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1267916497 / 1000000000) : ℝ) ≤ Real.exp (2 * (1899 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1899 / 16000)) (1267916497 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1901 / 16000) : ℝ)) ≤ (1268233517 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1901 / 16000)) (1268233517 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((77368011 / 500) : ℝ) ≤ Real.exp (3 * (3983159 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3983159 / 1000000)) (77368011 / 500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1899 / 16000) : ℝ) (1901 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3983159 / 1000000) (3984283 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1899 / 16000) (1901 / 16000) (1267916497 / 1000000000) (1268233517 / 1000000000) (3983159 / 1000000) (3984283 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1899 / 16000) (1901 / 16000) (3983159 / 1000000) (3984283 / 1000000) (9889 / 250) (198 / 5)
    (11134 / 125) (44893 / 500) (-115183 / 200) (105059 / 500000) (2016001 / 500) (1654431 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3983159 / 1000000) (77368011 / 500) (1654431 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3983159 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3983159 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityExpCompact_cellsBatch007 :
    ∀ t ∈ Set.Icc ((1861 / 16000) : ℝ) (1901 / 16000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell140
      hpThetaDensityExpCompact_cell141)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell142
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell143
      hpThetaDensityExpCompact_cell144)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell145
      hpThetaDensityExpCompact_cell146)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell147
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell148
      hpThetaDensityExpCompact_cell149))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell150
      hpThetaDensityExpCompact_cell151)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell152
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell153
      hpThetaDensityExpCompact_cell154)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell155
      hpThetaDensityExpCompact_cell156)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell157
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell158
      hpThetaDensityExpCompact_cell159)))))

#print axioms hpThetaDensityExpCompact_cellsBatch007
end HodgeProofHP
