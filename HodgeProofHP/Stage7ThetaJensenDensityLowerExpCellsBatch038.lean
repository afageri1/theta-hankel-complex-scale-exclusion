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
theorem hpThetaDensityLowerExpCompact_cell760 :
    ∀ t ∈ Set.Icc ((44707 / 512000) : ℝ) (44723 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1190813537 / 1000000000) : ℝ) ≤ Real.exp (2 * (44707 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44707 / 512000)) (1190813537 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44723 / 512000) : ℝ)) ≤ (595443983 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44723 / 512000)) (595443983 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((37409221341 / 500000) : ℝ) ≤ Real.exp (3 * (187047 / 50000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (187047 / 50000)) (37409221341 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44707 / 512000) : ℝ) (44723 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (187047 / 50000) (1870647 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44707 / 512000) (44723 / 512000) (1190813537 / 1000000000) (595443983 / 500000000) (187047 / 50000) (1870647 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44707 / 512000) (44723 / 512000) (187047 / 50000) (1870647 / 500000) (3353 / 100) (4193 / 125)
    (2751 / 50) (6903 / 125) (-69937 / 125) (1799 / 5000) (1567391 / 500) (3421617 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (187047 / 50000) (37409221341 / 500000) (3421617 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (187047 / 50000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (187047 / 50000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell761 :
    ∀ t ∈ Set.Icc ((44723 / 512000) : ℝ) (44739 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((238177593 / 200000000) : ℝ) ≤ Real.exp (2 * (44723 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44723 / 512000)) (238177593 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44739 / 512000) : ℝ)) ≤ (1190962399 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44739 / 512000)) (1190962399 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((37435491819 / 500000) : ℝ) ≤ Real.exp (3 * (1870587 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1870587 / 500000)) (37435491819 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44723 / 512000) : ℝ) (44739 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1870587 / 500000) (467691 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44723 / 512000) (44739 / 512000) (238177593 / 200000000) (1190962399 / 1000000000) (1870587 / 500000) (467691 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44723 / 512000) (44739 / 512000) (1870587 / 500000) (467691 / 125000) (4192 / 125) (671 / 20)
    (55049 / 1000) (27627 / 500) (-139883 / 250) (71923 / 200000) (3135567 / 1000) (213701 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1870587 / 500000) (37435491819 / 500000) (213701 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1870587 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1870587 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell762 :
    ∀ t ∈ Set.Icc ((44739 / 512000) : ℝ) (8951 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((595481199 / 500000000) : ℝ) ≤ Real.exp (2 * (44739 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44739 / 512000)) (595481199 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8951 / 102400) : ℝ)) ≤ (1191036837 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8951 / 102400)) (1191036837 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((7492356149 / 100000) : ℝ) ≤ Real.exp (3 * (116919 / 31250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (116919 / 31250)) (7492356149 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44739 / 512000) : ℝ) (8951 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (116919 / 31250) (1870881 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44739 / 512000) (8951 / 102400) (595481199 / 500000000) (1191036837 / 1000000000) (116919 / 31250) (1870881 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44739 / 512000) (8951 / 102400) (116919 / 31250) (1870881 / 500000) (33541 / 1000) (6711 / 200)
    (55079 / 1000) (13821 / 250) (-69946 / 125) (35943 / 100000) (3136351 / 1000) (213551 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (116919 / 31250) (7492356149 / 100000) (213551 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (116919 / 31250)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (116919 / 31250)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell763 :
    ∀ t ∈ Set.Icc ((8951 / 102400) : ℝ) (44771 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((297759209 / 250000000) : ℝ) ≤ Real.exp (2 * (8951 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8951 / 102400)) (297759209 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44771 / 512000) : ℝ)) ≤ (1191111279 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44771 / 512000)) (1191111279 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((14995235253 / 200000) : ℝ) ≤ Real.exp (3 * (1870821 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1870821 / 500000)) (14995235253 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8951 / 102400) : ℝ) (44771 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1870821 / 500000) (935499 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8951 / 102400) (44771 / 512000) (297759209 / 250000000) (1191111279 / 1000000000) (1870821 / 500000) (935499 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8951 / 102400) (44771 / 512000) (1870821 / 500000) (935499 / 250000) (33547 / 1000) (33561 / 1000)
    (55109 / 1000) (55313 / 1000) (-139901 / 250) (71849 / 200000) (392142 / 125) (1707209 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1870821 / 500000) (14995235253 / 200000) (1707209 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1870821 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1870821 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell764 :
    ∀ t ∈ Set.Icc ((44771 / 512000) : ℝ) (44787 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((595555639 / 500000000) : ℝ) ≤ Real.exp (2 * (44771 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44771 / 512000)) (595555639 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44787 / 512000) : ℝ)) ≤ (595592863 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44787 / 512000)) (595592863 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((75028827989 / 1000000) : ℝ) ≤ Real.exp (3 * (935469 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (935469 / 250000)) (75028827989 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44771 / 512000) : ℝ) (44787 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (935469 / 250000) (374223 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44771 / 512000) (44787 / 512000) (595555639 / 500000000) (595592863 / 500000000) (935469 / 250000) (374223 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44771 / 512000) (44787 / 512000) (935469 / 250000) (374223 / 100000) (33553 / 1000) (16783 / 500)
    (27569 / 500) (55343 / 1000) (-13991 / 25) (17953 / 50000) (3137921 / 1000) (1706011 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (935469 / 250000) (75028827989 / 1000000) (1706011 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (935469 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (935469 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell765 :
    ∀ t ∈ Set.Icc ((44787 / 512000) : ℝ) (44803 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((47647429 / 40000000) : ℝ) ≤ Real.exp (2 * (44787 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44787 / 512000)) (47647429 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44803 / 512000) : ℝ)) ≤ (1191260177 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44803 / 512000)) (1191260177 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((75081291443 / 1000000) : ℝ) ≤ Real.exp (3 * (3742109 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3742109 / 1000000)) (75081291443 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44787 / 512000) : ℝ) (44803 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3742109 / 1000000) (3742463 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44787 / 512000) (44803 / 512000) (47647429 / 40000000) (1191260177 / 1000000000) (3742109 / 1000000) (3742463 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44787 / 512000) (44803 / 512000) (3742109 / 1000000) (3742463 / 1000000) (16779 / 500) (8393 / 250)
    (6896 / 125) (13843 / 250) (-22387 / 40) (358877 / 1000000) (1569351 / 500) (1704819 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3742109 / 1000000) (75081291443 / 1000000) (1704819 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3742109 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3742109 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell766 :
    ∀ t ∈ Set.Icc ((44803 / 512000) : ℝ) (44819 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((74453761 / 62500000) : ℝ) ≤ Real.exp (2 * (44803 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44803 / 512000)) (74453761 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44819 / 512000) : ℝ)) ≤ (1191334633 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44819 / 512000)) (1191334633 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((75134016983 / 1000000) : ℝ) ≤ Real.exp (3 * (3742343 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3742343 / 1000000)) (75134016983 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44803 / 512000) : ℝ) (44819 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3742343 / 1000000) (3742697 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44803 / 512000) (44819 / 512000) (74453761 / 62500000) (1191334633 / 1000000000) (3742343 / 1000000) (3742697 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44803 / 512000) (44819 / 512000) (3742343 / 1000000) (3742697 / 1000000) (8391 / 250) (16789 / 500)
    (55197 / 1000) (27701 / 500) (-559711 / 1000) (89673 / 250000) (3139487 / 1000) (681449 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3742343 / 1000000) (75134016983 / 1000000) (681449 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3742343 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3742343 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell767 :
    ∀ t ∈ Set.Icc ((44819 / 512000) : ℝ) (8967 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((148916829 / 125000000) : ℝ) ≤ Real.exp (2 * (44819 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44819 / 512000)) (148916829 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8967 / 102400) : ℝ)) ≤ (595704547 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8967 / 102400)) (595704547 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1503735591 / 20000) : ℝ) ≤ Real.exp (3 * (3742577 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3742577 / 1000000)) (1503735591 / 20000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44819 / 512000) : ℝ) (8967 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3742577 / 1000000) (3742931 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44819 / 512000) (8967 / 102400) (148916829 / 125000000) (595704547 / 500000000) (3742577 / 1000000) (3742931 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44819 / 512000) (8967 / 102400) (3742577 / 1000000) (3742931 / 1000000) (33569 / 1000) (33583 / 1000)
    (55227 / 1000) (6929 / 125) (-559747 / 1000) (89627 / 250000) (3140273 / 1000) (1702427 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3742577 / 1000000) (1503735591 / 20000) (1702427 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3742577 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3742577 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell768 :
    ∀ t ∈ Set.Icc ((8967 / 102400) : ℝ) (44851 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1191409093 / 1000000000) : ℝ) ≤ Real.exp (2 * (8967 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8967 / 102400)) (1191409093 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44851 / 512000) : ℝ)) ≤ (1191483559 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44851 / 512000)) (1191483559 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((75239579169 / 1000000) : ℝ) ≤ Real.exp (3 * (3742811 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3742811 / 1000000)) (75239579169 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8967 / 102400) : ℝ) (44851 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3742811 / 1000000) (748633 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8967 / 102400) (44851 / 512000) (1191409093 / 1000000000) (1191483559 / 1000000000) (3742811 / 1000000) (748633 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8967 / 102400) (44851 / 512000) (3742811 / 1000000) (748633 / 200000) (1343 / 40) (33589 / 1000)
    (6907 / 125) (55461 / 1000) (-559783 / 1000) (358323 / 1000000) (1570529 / 500) (680493 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3742811 / 1000000) (75239579169 / 1000000) (680493 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3742811 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3742811 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell769 :
    ∀ t ∈ Set.Icc ((44851 / 512000) : ℝ) (44867 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((595741779 / 500000000) : ℝ) ≤ Real.exp (2 * (44851 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44851 / 512000)) (595741779 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44867 / 512000) : ℝ)) ≤ (1191558029 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44867 / 512000)) (1191558029 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((37646207933 / 500000) : ℝ) ≤ Real.exp (3 * (748609 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (748609 / 200000)) (37646207933 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44851 / 512000) : ℝ) (44867 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (748609 / 200000) (3743399 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44851 / 512000) (44867 / 512000) (595741779 / 500000000) (1191558029 / 1000000000) (748609 / 200000) (3743399 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44851 / 512000) (44867 / 512000) (748609 / 200000) (3743399 / 1000000) (33581 / 1000) (16797 / 500)
    (27643 / 500) (55491 / 1000) (-279909 / 500) (358139 / 1000000) (3141843 / 1000) (3400077 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (748609 / 200000) (37646207933 / 500000) (3400077 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (748609 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (748609 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell770 :
    ∀ t ∈ Set.Icc ((44867 / 512000) : ℝ) (44883 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((297889507 / 250000000) : ℝ) ≤ Real.exp (2 * (44867 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44867 / 512000)) (297889507 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44883 / 512000) : ℝ)) ≤ (148954063 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44883 / 512000)) (148954063 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((75345289667 / 1000000) : ℝ) ≤ Real.exp (3 * (3743279 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3743279 / 1000000)) (75345289667 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44867 / 512000) : ℝ) (44883 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3743279 / 1000000) (3743633 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44867 / 512000) (44883 / 512000) (297889507 / 250000000) (148954063 / 125000000) (3743279 / 1000000) (3743633 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44867 / 512000) (44883 / 512000) (3743279 / 1000000) (3743633 / 1000000) (16793 / 500) (168 / 5)
    (13829 / 250) (55521 / 1000) (-279927 / 500) (71591 / 200000) (3142629 / 1000) (3397691 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3743279 / 1000000) (75345289667 / 1000000) (3397691 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3743279 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3743279 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell771 :
    ∀ t ∈ Set.Icc ((44883 / 512000) : ℝ) (44899 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1191632503 / 1000000000) : ℝ) ≤ Real.exp (2 * (44883 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44883 / 512000)) (1191632503 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44899 / 512000) : ℝ)) ≤ (1191706983 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44899 / 512000)) (1191706983 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((75398200599 / 1000000) : ℝ) ≤ Real.exp (3 * (3743513 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3743513 / 1000000)) (75398200599 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44883 / 512000) : ℝ) (44899 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3743513 / 1000000) (3743867 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44883 / 512000) (44899 / 512000) (1191632503 / 1000000000) (1191706983 / 1000000000) (3743513 / 1000000) (3743867 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44883 / 512000) (44899 / 512000) (3743513 / 1000000) (3743867 / 1000000) (4199 / 125) (16803 / 500)
    (11069 / 200) (1111 / 20) (-55989 / 100) (357771 / 1000000) (628683 / 200) (3395307 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3743513 / 1000000) (75398200599 / 1000000) (3395307 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3743513 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3743513 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell772 :
    ∀ t ∈ Set.Icc ((44899 / 512000) : ℝ) (8983 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((595853491 / 500000000) : ℝ) ≤ Real.exp (2 * (44899 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44899 / 512000)) (595853491 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8983 / 102400) : ℝ)) ≤ (1191781467 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8983 / 102400)) (1191781467 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((75451148687 / 1000000) : ℝ) ≤ Real.exp (3 * (3743747 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3743747 / 1000000)) (75451148687 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44899 / 512000) : ℝ) (8983 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3743747 / 1000000) (3744101 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44899 / 512000) (8983 / 102400) (595853491 / 500000000) (1191781467 / 1000000000) (3743747 / 1000000) (3744101 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44899 / 512000) (8983 / 102400) (3743747 / 1000000) (3744101 / 1000000) (33597 / 1000) (33611 / 1000)
    (443 / 8) (2779 / 50) (-22397 / 40) (178793 / 500000) (3144201 / 1000) (848231 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3743747 / 1000000) (75451148687 / 1000000) (848231 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3743747 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3743747 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell773 :
    ∀ t ∈ Set.Icc ((8983 / 102400) : ℝ) (44931 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((595890733 / 500000000) : ℝ) ≤ Real.exp (2 * (8983 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8983 / 102400)) (595890733 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44931 / 512000) : ℝ)) ≤ (297963989 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44931 / 512000)) (297963989 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((37752066979 / 500000) : ℝ) ≤ Real.exp (3 * (3743981 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3743981 / 1000000)) (37752066979 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8983 / 102400) : ℝ) (44931 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3743981 / 1000000) (748867 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8983 / 102400) (44931 / 512000) (595890733 / 500000000) (297963989 / 250000000) (3743981 / 1000000) (748867 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8983 / 102400) (44931 / 512000) (3743981 / 1000000) (748867 / 200000) (33603 / 1000) (33617 / 1000)
    (11081 / 200) (5561 / 100) (-559961 / 1000) (357403 / 1000000) (3144987 / 1000) (3390543 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3743981 / 1000000) (37752066979 / 500000) (3390543 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3743981 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3743981 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell774 :
    ∀ t ∈ Set.Icc ((44931 / 512000) : ℝ) (44947 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((238371191 / 200000000) : ℝ) ≤ Real.exp (2 * (44931 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44931 / 512000)) (238371191 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44947 / 512000) : ℝ)) ≤ (1191930449 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44947 / 512000)) (1191930449 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((75557156437 / 1000000) : ℝ) ≤ Real.exp (3 * (748843 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (748843 / 200000)) (75557156437 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44931 / 512000) : ℝ) (44947 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (748843 / 200000) (3744569 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44931 / 512000) (44947 / 512000) (238371191 / 200000000) (1191930449 / 1000000000) (748843 / 200000) (3744569 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44931 / 512000) (44947 / 512000) (748843 / 200000) (3744569 / 1000000) (33609 / 1000) (16811 / 500)
    (27717 / 500) (55639 / 1000) (-139999 / 250) (357219 / 1000000) (3145773 / 1000) (847041 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (748843 / 200000) (75557156437 / 1000000) (847041 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (748843 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (748843 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell775 :
    ∀ t ∈ Set.Icc ((44947 / 512000) : ℝ) (44963 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((74495653 / 62500000) : ℝ) ≤ Real.exp (2 * (44947 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44947 / 512000)) (74495653 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44963 / 512000) : ℝ)) ≤ (1192004947 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44963 / 512000)) (1192004947 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((75610216151 / 1000000) : ℝ) ≤ Real.exp (3 * (3744449 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3744449 / 1000000)) (75610216151 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44947 / 512000) : ℝ) (44963 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3744449 / 1000000) (3744803 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44947 / 512000) (44963 / 512000) (74495653 / 62500000) (1192004947 / 1000000000) (3744449 / 1000000) (3744803 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44947 / 512000) (44963 / 512000) (3744449 / 1000000) (3744803 / 1000000) (16807 / 500) (8407 / 250)
    (6933 / 125) (55669 / 1000) (-70004 / 125) (71407 / 200000) (78664 / 25) (1692893 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3744449 / 1000000) (75610216151 / 1000000) (1692893 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3744449 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3744449 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell776 :
    ∀ t ∈ Set.Icc ((44963 / 512000) : ℝ) (44979 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((596002473 / 500000000) : ℝ) ≤ Real.exp (2 * (44963 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44963 / 512000)) (596002473 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((44979 / 512000) : ℝ)) ≤ (23841589 / 20000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (44979 / 512000)) (23841589 / 20000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((75663313127 / 1000000) : ℝ) ≤ Real.exp (3 * (3744683 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3744683 / 1000000)) (75663313127 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44963 / 512000) : ℝ) (44979 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3744683 / 1000000) (3745037 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44963 / 512000) (44979 / 512000) (596002473 / 500000000) (23841589 / 20000000) (3744683 / 1000000) (3745037 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44963 / 512000) (44979 / 512000) (3744683 / 1000000) (3745037 / 1000000) (1681 / 50) (16817 / 500)
    (27747 / 500) (55699 / 1000) (-560067 / 1000) (356851 / 1000000) (1573673 / 500) (338341 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3744683 / 1000000) (75663313127 / 1000000) (338341 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3744683 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3744683 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell777 :
    ∀ t ∈ Set.Icc ((44979 / 512000) : ℝ) (8999 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1192079449 / 1000000000) : ℝ) ≤ Real.exp (2 * (44979 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (44979 / 512000)) (1192079449 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8999 / 102400) : ℝ)) ≤ (1192153957 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8999 / 102400)) (1192153957 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((75716447389 / 1000000) : ℝ) ≤ Real.exp (3 * (3744917 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3744917 / 1000000)) (75716447389 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((44979 / 512000) : ℝ) (8999 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3744917 / 1000000) (3745271 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (44979 / 512000) (8999 / 102400) (1192079449 / 1000000000) (1192153957 / 1000000000) (3744917 / 1000000) (3745271 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (44979 / 512000) (8999 / 102400) (3744917 / 1000000) (3745271 / 1000000) (269 / 8) (33639 / 1000)
    (55523 / 1000) (6966 / 125) (-560103 / 1000) (89167 / 250000) (3148133 / 1000) (845259 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3744917 / 1000000) (75716447389 / 1000000) (845259 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3744917 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3744917 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell778 :
    ∀ t ∈ Set.Icc ((8999 / 102400) : ℝ) (45011 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((298038489 / 250000000) : ℝ) ≤ Real.exp (2 * (8999 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8999 / 102400)) (298038489 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45011 / 512000) : ℝ)) ≤ (1192228469 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45011 / 512000)) (1192228469 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((18942404741 / 250000) : ℝ) ≤ Real.exp (3 * (3745151 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3745151 / 1000000)) (18942404741 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8999 / 102400) : ℝ) (45011 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3745151 / 1000000) (749101 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8999 / 102400) (45011 / 512000) (298038489 / 250000000) (1192228469 / 1000000000) (3745151 / 1000000) (749101 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8999 / 102400) (45011 / 512000) (3745151 / 1000000) (749101 / 200000) (33631 / 1000) (6729 / 200)
    (55553 / 1000) (27879 / 500) (-280069 / 500) (89121 / 250000) (78723 / 25) (3378663 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3745151 / 1000000) (18942404741 / 250000) (3378663 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3745151 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3745151 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell779 :
    ∀ t ∈ Set.Icc ((45011 / 512000) : ℝ) (45027 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((298057117 / 250000000) : ℝ) ≤ Real.exp (2 * (45011 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45011 / 512000)) (298057117 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45027 / 512000) : ℝ)) ≤ (596151493 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45027 / 512000)) (596151493 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((75822827879 / 1000000) : ℝ) ≤ Real.exp (3 * (749077 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (749077 / 200000)) (75822827879 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45011 / 512000) : ℝ) (45027 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (749077 / 200000) (187287 / 50000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45011 / 512000) (45027 / 512000) (298057117 / 250000000) (596151493 / 500000000) (749077 / 200000) (187287 / 50000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45011 / 512000) (45027 / 512000) (749077 / 200000) (187287 / 50000) (33637 / 1000) (673 / 20)
    (55583 / 1000) (13947 / 250) (-560169 / 1000) (356301 / 1000000) (314971 / 100) (844073 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (749077 / 200000) (75822827879 / 1000000) (844073 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (749077 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (749077 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch038 :
    ∀ t ∈ Set.Icc ((44707 / 512000) : ℝ) (45027 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell760
      hpThetaDensityLowerExpCompact_cell761)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell762
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell763
      hpThetaDensityLowerExpCompact_cell764)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell765
      hpThetaDensityLowerExpCompact_cell766)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell767
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell768
      hpThetaDensityLowerExpCompact_cell769))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell770
      hpThetaDensityLowerExpCompact_cell771)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell772
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell773
      hpThetaDensityLowerExpCompact_cell774)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell775
      hpThetaDensityLowerExpCompact_cell776)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell777
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell778
      hpThetaDensityLowerExpCompact_cell779)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch038
end HodgeProofHP
