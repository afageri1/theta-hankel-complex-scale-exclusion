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
theorem hpThetaDensityLowerExpCompact_cell400 :
    ∀ t ∈ Set.Icc ((41739 / 512000) : ℝ) (41743 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((588543633 / 500000000) : ℝ) ≤ Real.exp (2 * (41739 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41739 / 512000)) (588543633 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41743 / 512000) : ℝ)) ≤ (1177105659 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41743 / 512000)) (1177105659 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6573959987 / 100000) : ℝ) ≤ Real.exp (3 * (3697819 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3697819 / 1000000)) (6573959987 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41739 / 512000) : ℝ) (41743 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3697819 / 1000000) (924499 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41739 / 512000) (41743 / 512000) (588543633 / 500000000) (1177105659 / 1000000000) (3697819 / 1000000) (924499 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41739 / 512000) (41743 / 512000) (3697819 / 1000000) (924499 / 250000) (32507 / 1000) (16257 / 500)
    (49719 / 1000) (2491 / 50) (-553207 / 1000) (98859 / 250000) (2992167 / 1000) (3894153 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3697819 / 1000000) (6573959987 / 100000) (3894153 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3697819 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3697819 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell401 :
    ∀ t ∈ Set.Icc ((41743 / 512000) : ℝ) (41747 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((588552829 / 500000000) : ℝ) ≤ Real.exp (2 * (41743 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41743 / 512000)) (588552829 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41747 / 512000) : ℝ)) ≤ (294281013 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41747 / 512000)) (294281013 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1315020791 / 20000) : ℝ) ≤ Real.exp (3 * (3697877 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3697877 / 1000000)) (1315020791 / 20000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41743 / 512000) : ℝ) (41747 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3697877 / 1000000) (3698053 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41743 / 512000) (41747 / 512000) (588552829 / 500000000) (294281013 / 250000000) (3697877 / 1000000) (3698053 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41743 / 512000) (41747 / 512000) (3697877 / 1000000) (3698053 / 1000000) (8127 / 250) (8129 / 250)
    (49727 / 1000) (49827 / 1000) (-276611 / 500) (197693 / 500000) (2992351 / 1000) (155739 / 40000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3697877 / 1000000) (1315020791 / 20000) (155739 / 40000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3697877 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3697877 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell402 :
    ∀ t ∈ Set.Icc ((41747 / 512000) : ℝ) (41751 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1177124051 / 1000000000) : ℝ) ≤ Real.exp (2 * (41747 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41747 / 512000)) (1177124051 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41751 / 512000) : ℝ)) ≤ (294285611 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41751 / 512000)) (294285611 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((65762481221 / 1000000) : ℝ) ≤ Real.exp (3 * (739587 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (739587 / 200000)) (65762481221 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41747 / 512000) : ℝ) (41751 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (739587 / 200000) (3698111 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41747 / 512000) (41751 / 512000) (1177124051 / 1000000000) (294285611 / 250000000) (739587 / 200000) (3698111 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41747 / 512000) (41751 / 512000) (739587 / 200000) (3698111 / 1000000) (3251 / 100) (32517 / 1000)
    (24867 / 500) (24917 / 500) (-69154 / 125) (49417 / 125000) (2992539 / 1000) (1946399 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (739587 / 200000) (65762481221 / 1000000) (1946399 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (739587 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (739587 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell403 :
    ∀ t ∈ Set.Icc ((41751 / 512000) : ℝ) (8351 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1177142443 / 1000000000) : ℝ) ≤ Real.exp (2 * (41751 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41751 / 512000)) (1177142443 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8351 / 102400) : ℝ)) ≤ (1177160837 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8351 / 102400)) (1177160837 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32886863781 / 500000) : ℝ) ≤ Real.exp (3 * (462249 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (462249 / 125000)) (32886863781 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41751 / 512000) : ℝ) (8351 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (462249 / 125000) (3698169 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41751 / 512000) (8351 / 102400) (1177142443 / 1000000000) (1177160837 / 1000000000) (462249 / 125000) (3698169 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41751 / 512000) (8351 / 102400) (462249 / 125000) (3698169 / 1000000) (32511 / 1000) (16259 / 500)
    (2487 / 50) (49841 / 1000) (-276619 / 500) (395287 / 1000000) (2992727 / 1000) (973033 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (462249 / 125000) (32886863781 / 500000) (973033 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (462249 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (462249 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell404 :
    ∀ t ∈ Set.Icc ((8351 / 102400) : ℝ) (41759 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((294290209 / 250000000) : ℝ) ≤ Real.exp (2 * (8351 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8351 / 102400)) (294290209 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41759 / 512000) : ℝ)) ≤ (1177179231 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41759 / 512000)) (1177179231 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((65785173181 / 1000000) : ℝ) ≤ Real.exp (3 * (73961 / 20000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (73961 / 20000)) (65785173181 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8351 / 102400) : ℝ) (41759 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (73961 / 20000) (3698227 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8351 / 102400) (41759 / 512000) (294290209 / 250000000) (1177179231 / 1000000000) (73961 / 20000) (3698227 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8351 / 102400) (41759 / 512000) (73961 / 20000) (3698227 / 1000000) (4064 / 125) (813 / 25)
    (49747 / 1000) (6231 / 125) (-69156 / 125) (98809 / 250000) (598583 / 200) (778291 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (73961 / 20000) (65785173181 / 1000000) (778291 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (73961 / 20000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (73961 / 20000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell405 :
    ∀ t ∈ Set.Icc ((41759 / 512000) : ℝ) (41763 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((117717923 / 100000000) : ℝ) ≤ Real.exp (2 * (41759 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41759 / 512000)) (117717923 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41763 / 512000) : ℝ)) ≤ (147149703 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41763 / 512000)) (147149703 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8224577599 / 125000) : ℝ) ≤ Real.exp (3 * (924527 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (924527 / 250000)) (8224577599 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41759 / 512000) : ℝ) (41763 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (924527 / 250000) (739657 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41759 / 512000) (41763 / 512000) (117717923 / 100000000) (147149703 / 125000000) (924527 / 250000) (739657 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41759 / 512000) (41763 / 512000) (924527 / 250000) (739657 / 200000) (16257 / 500) (32521 / 1000)
    (24877 / 500) (9971 / 200) (-276629 / 500) (197593 / 500000) (1496551 / 500) (1945389 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (924527 / 250000) (8224577599 / 125000) (1945389 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (924527 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (924527 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell406 :
    ∀ t ∈ Set.Icc ((41763 / 512000) : ℝ) (41767 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1177197623 / 1000000000) : ℝ) ≤ Real.exp (2 * (41763 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41763 / 512000)) (1177197623 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41767 / 512000) : ℝ)) ≤ (588608009 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41767 / 512000)) (588608009 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32904035197 / 500000) : ℝ) ≤ Real.exp (3 * (1849083 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1849083 / 500000)) (32904035197 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41763 / 512000) : ℝ) (41767 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1849083 / 500000) (1849171 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41763 / 512000) (41767 / 512000) (1177197623 / 1000000000) (588608009 / 500000000) (1849083 / 500000) (1849171 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41763 / 512000) (41767 / 512000) (1849083 / 500000) (1849171 / 500000) (6503 / 200) (16261 / 500)
    (24881 / 500) (24931 / 500) (-69159 / 125) (6174 / 15625) (2993287 / 1000) (3890101 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1849083 / 500000) (32904035197 / 500000) (3890101 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1849083 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1849083 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell407 :
    ∀ t ∈ Set.Icc ((41767 / 512000) : ℝ) (41771 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1177216017 / 1000000000) : ℝ) ≤ Real.exp (2 * (41767 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41767 / 512000)) (1177216017 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41771 / 512000) : ℝ)) ≤ (294308603 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41771 / 512000)) (294308603 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6581952199 / 100000) : ℝ) ≤ Real.exp (3 * (231139 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (231139 / 62500)) (6581952199 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41767 / 512000) : ℝ) (41771 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (231139 / 62500) (4623 / 1250) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41767 / 512000) (41771 / 512000) (1177216017 / 1000000000) (294308603 / 250000000) (231139 / 62500) (4623 / 1250) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41767 / 512000) (41771 / 512000) (231139 / 62500) (4623 / 1250) (32517 / 1000) (8131 / 250)
    (49769 / 1000) (49869 / 1000) (-553283 / 1000) (197543 / 500000) (119739 / 40) (243089 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (231139 / 62500) (6581952199 / 100000) (243089 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (231139 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (231139 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell408 :
    ∀ t ∈ Set.Icc ((41771 / 512000) : ℝ) (1671 / 20480), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1177234411 / 1000000000) : ℝ) ≤ Real.exp (2 * (41771 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41771 / 512000)) (1177234411 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1671 / 20480) : ℝ)) ≤ (1177252807 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1671 / 20480)) (1177252807 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((13166155617 / 200000) : ℝ) ≤ Real.exp (3 * (3698281 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3698281 / 1000000)) (13166155617 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41771 / 512000) : ℝ) (1671 / 20480),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3698281 / 1000000) (1849229 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41771 / 512000) (1671 / 20480) (1177234411 / 1000000000) (1177252807 / 1000000000) (3698281 / 1000000) (1849229 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41771 / 512000) (1671 / 20480) (3698281 / 1000000) (1849229 / 500000) (16259 / 500) (1301 / 40)
    (1991 / 40) (12469 / 250) (-69161 / 125) (395037 / 1000000) (1496831 / 500) (3888759 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3698281 / 1000000) (13166155617 / 200000) (3888759 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3698281 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3698281 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell409 :
    ∀ t ∈ Set.Icc ((1671 / 20480) : ℝ) (41779 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((588626403 / 500000000) : ℝ) ≤ Real.exp (2 * (1671 / 20480)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1671 / 20480)) (588626403 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41779 / 512000) : ℝ)) ≤ (1177271201 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41779 / 512000)) (1177271201 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2057569801 / 31250) : ℝ) ≤ Real.exp (3 * (3698339 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3698339 / 1000000)) (2057569801 / 31250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1671 / 20480) : ℝ) (41779 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3698339 / 1000000) (924629 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1671 / 20480) (41779 / 512000) (588626403 / 500000000) (1177271201 / 1000000000) (3698339 / 1000000) (924629 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1671 / 20480) (41779 / 512000) (3698339 / 1000000) (924629 / 250000) (32519 / 1000) (32527 / 1000)
    (24891 / 500) (12471 / 250) (-276649 / 500) (197493 / 500000) (59877 / 20) (1944041 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3698339 / 1000000) (2057569801 / 31250) (1944041 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3698339 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3698339 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell410 :
    ∀ t ∈ Set.Icc ((41779 / 512000) : ℝ) (41783 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1471589 / 1250000) : ℝ) ≤ Real.exp (2 * (41779 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41779 / 512000)) (1471589 / 1250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41783 / 512000) : ℝ)) ≤ (294322399 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41783 / 512000)) (294322399 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16463422793 / 250000) : ℝ) ≤ Real.exp (3 * (3698397 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3698397 / 1000000)) (16463422793 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41779 / 512000) : ℝ) (41783 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3698397 / 1000000) (3698573 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41779 / 512000) (41783 / 512000) (1471589 / 1250000) (294322399 / 250000000) (3698397 / 1000000) (3698573 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41779 / 512000) (41783 / 512000) (3698397 / 1000000) (3698573 / 1000000) (32521 / 1000) (4066 / 125)
    (4979 / 100) (4989 / 100) (-553313 / 1000) (49367 / 125000) (598807 / 200) (1943703 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3698397 / 1000000) (16463422793 / 250000) (1943703 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3698397 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3698397 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell411 :
    ∀ t ∈ Set.Icc ((41783 / 512000) : ℝ) (41787 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((235457919 / 200000000) : ℝ) ≤ Real.exp (2 * (41783 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41783 / 512000)) (235457919 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41787 / 512000) : ℝ)) ≤ (147163499 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41787 / 512000)) (147163499 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32932575353 / 500000) : ℝ) ≤ Real.exp (3 * (739691 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (739691 / 200000)) (32932575353 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41783 / 512000) : ℝ) (41787 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (739691 / 200000) (3698631 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41783 / 512000) (41787 / 512000) (235457919 / 200000000) (147163499 / 125000000) (739691 / 200000) (3698631 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41783 / 512000) (41787 / 512000) (739691 / 200000) (3698631 / 1000000) (16261 / 500) (32529 / 1000)
    (49797 / 1000) (49897 / 1000) (-553323 / 1000) (197443 / 500000) (2994223 / 1000) (388673 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (739691 / 200000) (32932575353 / 500000) (388673 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (739691 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (739691 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell412 :
    ∀ t ∈ Set.Icc ((41787 / 512000) : ℝ) (41791 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1177307991 / 1000000000) : ℝ) ≤ Real.exp (2 * (41787 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41787 / 512000)) (1177307991 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41791 / 512000) : ℝ)) ≤ (1177326387 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41791 / 512000)) (1177326387 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32938306117 / 500000) : ℝ) ≤ Real.exp (3 * (3698513 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3698513 / 1000000)) (32938306117 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41787 / 512000) : ℝ) (41791 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3698513 / 1000000) (3698689 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41787 / 512000) (41791 / 512000) (1177307991 / 1000000000) (1177326387 / 1000000000) (3698513 / 1000000) (3698689 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41787 / 512000) (41791 / 512000) (3698513 / 1000000) (3698689 / 1000000) (32523 / 1000) (32531 / 1000)
    (12451 / 250) (6238 / 125) (-553333 / 1000) (98709 / 250000) (299441 / 100) (3886053 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3698513 / 1000000) (32938306117 / 500000) (3886053 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3698513 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3698513 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell413 :
    ∀ t ∈ Set.Icc ((41791 / 512000) : ℝ) (8359 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((588663193 / 500000000) : ℝ) ≤ Real.exp (2 * (41791 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41791 / 512000)) (588663193 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8359 / 102400) : ℝ)) ≤ (1177344783 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8359 / 102400)) (1177344783 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((65887878093 / 1000000) : ℝ) ≤ Real.exp (3 * (369857 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (369857 / 100000)) (65887878093 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41791 / 512000) : ℝ) (8359 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (369857 / 100000) (3698747 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41791 / 512000) (8359 / 102400) (588663193 / 500000000) (1177344783 / 1000000000) (369857 / 100000) (3698747 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41791 / 512000) (8359 / 102400) (369857 / 100000) (3698747 / 1000000) (1301 / 40) (8133 / 250)
    (49811 / 1000) (6239 / 125) (-553339 / 1000) (394787 / 1000000) (1497299 / 500) (3885389 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (369857 / 100000) (65887878093 / 1000000) (3885389 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (369857 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (369857 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell414 :
    ∀ t ∈ Set.Icc ((8359 / 102400) : ℝ) (41799 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((588672391 / 500000000) : ℝ) ≤ Real.exp (2 * (8359 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8359 / 102400)) (588672391 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41799 / 512000) : ℝ)) ≤ (1177363179 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41799 / 512000)) (1177363179 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2635973743 / 40000) : ℝ) ≤ Real.exp (3 * (924657 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (924657 / 250000)) (2635973743 / 40000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8359 / 102400) : ℝ) (41799 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (924657 / 250000) (739761 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8359 / 102400) (41799 / 512000) (588672391 / 500000000) (1177363179 / 1000000000) (924657 / 250000) (739761 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8359 / 102400) (41799 / 512000) (924657 / 250000) (739761 / 200000) (16263 / 500) (32533 / 1000)
    (24909 / 500) (49919 / 1000) (-553349 / 1000) (394737 / 1000000) (1497393 / 500) (3884713 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (924657 / 250000) (2635973743 / 40000) (3884713 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (924657 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (924657 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell415 :
    ∀ t ∈ Set.Icc ((41799 / 512000) : ℝ) (41803 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((588681589 / 500000000) : ℝ) ≤ Real.exp (2 * (41799 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41799 / 512000)) (588681589 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41803 / 512000) : ℝ)) ≤ (147172697 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41803 / 512000)) (147172697 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32955405527 / 500000) : ℝ) ≤ Real.exp (3 * (1849343 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1849343 / 500000)) (32955405527 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41799 / 512000) : ℝ) (41803 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1849343 / 500000) (1849431 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41799 / 512000) (41803 / 512000) (588681589 / 500000000) (147172697 / 125000000) (1849343 / 500000) (1849431 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41799 / 512000) (41803 / 512000) (1849343 / 500000) (1849431 / 500000) (32527 / 1000) (6507 / 200)
    (1993 / 40) (1997 / 40) (-553363 / 1000) (197343 / 500000) (2994971 / 1000) (3884037 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1849343 / 500000) (32955405527 / 500000) (3884037 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1849343 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1849343 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell416 :
    ∀ t ∈ Set.Icc ((41803 / 512000) : ℝ) (41807 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((47095263 / 40000000) : ℝ) ≤ Real.exp (2 * (41803 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41803 / 512000)) (47095263 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41807 / 512000) : ℝ)) ≤ (294349993 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41807 / 512000)) (294349993 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((65922280527 / 1000000) : ℝ) ≤ Real.exp (3 * (462343 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (462343 / 125000)) (65922280527 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41803 / 512000) : ℝ) (41807 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (462343 / 125000) (92473 / 25000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41803 / 512000) (41807 / 512000) (47095263 / 40000000) (294349993 / 250000000) (462343 / 125000) (92473 / 25000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41803 / 512000) (41807 / 512000) (462343 / 125000) (92473 / 25000) (32529 / 1000) (4067 / 125)
    (6229 / 125) (12483 / 250) (-553373 / 1000) (98659 / 250000) (1497579 / 500) (3883361 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (462343 / 125000) (65922280527 / 1000000) (3883361 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (462343 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (462343 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell417 :
    ∀ t ∈ Set.Icc ((41807 / 512000) : ℝ) (41811 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1177399971 / 1000000000) : ℝ) ≤ Real.exp (2 * (41807 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41807 / 512000)) (1177399971 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41811 / 512000) : ℝ)) ≤ (1177418369 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41811 / 512000)) (1177418369 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((65933751997 / 1000000) : ℝ) ≤ Real.exp (3 * (1849401 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1849401 / 500000)) (65933751997 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41807 / 512000) : ℝ) (41811 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1849401 / 500000) (1849489 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41807 / 512000) (41811 / 512000) (1177399971 / 1000000000) (1177418369 / 1000000000) (1849401 / 500000) (1849489 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41807 / 512000) (41811 / 512000) (1849401 / 500000) (1849489 / 500000) (3253 / 100) (32537 / 1000)
    (49839 / 1000) (49939 / 1000) (-69173 / 125) (197293 / 500000) (1497673 / 500) (1941343 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1849401 / 500000) (65933751997 / 1000000) (1941343 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1849401 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1849401 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell418 :
    ∀ t ∈ Set.Icc ((41811 / 512000) : ℝ) (8363 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((9198581 / 7812500) : ℝ) ≤ Real.exp (2 * (41811 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41811 / 512000)) (9198581 / 7812500) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8363 / 102400) : ℝ)) ≤ (1177436767 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8363 / 102400)) (1177436767 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((65945027627 / 1000000) : ℝ) ≤ Real.exp (3 * (3698859 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3698859 / 1000000)) (65945027627 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41811 / 512000) : ℝ) (8363 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3698859 / 1000000) (924759 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41811 / 512000) (8363 / 102400) (9198581 / 7812500) (1177436767 / 1000000000) (3698859 / 1000000) (924759 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41811 / 512000) (8363 / 102400) (3698859 / 1000000) (924759 / 250000) (8133 / 250) (32539 / 1000)
    (24923 / 500) (49947 / 1000) (-553389 / 1000) (394537 / 1000000) (1497767 / 500) (1941011 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3698859 / 1000000) (65945027627 / 1000000) (1941011 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3698859 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3698859 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell419 :
    ∀ t ∈ Set.Icc ((8363 / 102400) : ℝ) (41819 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((588718383 / 500000000) : ℝ) ≤ Real.exp (2 * (8363 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8363 / 102400)) (588718383 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41819 / 512000) : ℝ)) ≤ (294363791 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41819 / 512000)) (294363791 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((13191300611 / 200000) : ℝ) ≤ Real.exp (3 * (3698917 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3698917 / 1000000)) (13191300611 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8363 / 102400) : ℝ) (41819 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3698917 / 1000000) (1849547 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8363 / 102400) (41819 / 512000) (588718383 / 500000000) (294363791 / 250000000) (3698917 / 1000000) (1849547 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8363 / 102400) (41819 / 512000) (3698917 / 1000000) (1849547 / 500000) (32533 / 1000) (1627 / 50)
    (49853 / 1000) (24977 / 500) (-553399 / 1000) (394487 / 1000000) (1497861 / 500) (1940673 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3698917 / 1000000) (13191300611 / 200000) (1940673 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3698917 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3698917 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch020 :
    ∀ t ∈ Set.Icc ((41739 / 512000) : ℝ) (41819 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell400
      hpThetaDensityLowerExpCompact_cell401)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell402
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell403
      hpThetaDensityLowerExpCompact_cell404)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell405
      hpThetaDensityLowerExpCompact_cell406)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell407
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell408
      hpThetaDensityLowerExpCompact_cell409))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell410
      hpThetaDensityLowerExpCompact_cell411)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell412
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell413
      hpThetaDensityLowerExpCompact_cell414)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell415
      hpThetaDensityLowerExpCompact_cell416)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell417
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell418
      hpThetaDensityLowerExpCompact_cell419)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch020
end HodgeProofHP
