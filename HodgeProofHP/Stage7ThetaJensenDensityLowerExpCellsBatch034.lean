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
theorem hpThetaDensityLowerExpCompact_cell680 :
    ∀ t ∈ Set.Icc ((43523 / 512000) : ℝ) (43531 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1185318741 / 1000000000) : ℝ) ≤ Real.exp (2 * (43523 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43523 / 512000)) (1185318741 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43531 / 512000) : ℝ)) ≤ (148169473 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43531 / 512000)) (148169473 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((71042510923 / 1000000) : ℝ) ≤ Real.exp (3 * (1861839 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1861839 / 500000)) (71042510923 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43523 / 512000) : ℝ) (43531 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1861839 / 500000) (1861957 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43523 / 512000) (43531 / 512000) (1185318741 / 1000000000) (148169473 / 125000000) (1861839 / 500000) (1861957 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43523 / 512000) (43531 / 512000) (1861839 / 500000) (1861957 / 500000) (33119 / 1000) (33129 / 1000)
    (26441 / 500) (26509 / 500) (-557307 / 1000) (373667 / 1000000) (3076937 / 1000) (3603477 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1861839 / 500000) (71042510923 / 1000000) (3603477 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1861839 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1861839 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell681 :
    ∀ t ∈ Set.Icc ((43531 / 512000) : ℝ) (43539 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1185355783 / 1000000000) : ℝ) ≤ Real.exp (2 * (43531 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43531 / 512000)) (1185355783 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43539 / 512000) : ℝ)) ≤ (1185392827 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43539 / 512000)) (1185392827 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8883431401 / 125000) : ℝ) ≤ Real.exp (3 * (744759 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (744759 / 200000)) (8883431401 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43531 / 512000) : ℝ) (43539 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (744759 / 200000) (3724031 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43531 / 512000) (43539 / 512000) (1185355783 / 1000000000) (1185392827 / 1000000000) (744759 / 200000) (3724031 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43531 / 512000) (43539 / 512000) (744759 / 200000) (3724031 / 1000000) (16561 / 500) (33131 / 1000)
    (52897 / 1000) (53033 / 1000) (-278663 / 500) (373571 / 1000000) (769331 / 250) (900553 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (744759 / 200000) (8883431401 / 125000) (900553 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (744759 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (744759 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell682 :
    ∀ t ∈ Set.Icc ((43539 / 512000) : ℝ) (43547 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((592696413 / 500000000) : ℝ) ≤ Real.exp (2 * (43539 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43539 / 512000)) (592696413 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43547 / 512000) : ℝ)) ≤ (1185429871 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43547 / 512000)) (1185429871 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((71092186971 / 1000000) : ℝ) ≤ Real.exp (3 * (3723911 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3723911 / 1000000)) (71092186971 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43539 / 512000) : ℝ) (43547 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3723911 / 1000000) (3724147 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43539 / 512000) (43547 / 512000) (592696413 / 500000000) (1185429871 / 1000000000) (3723911 / 1000000) (3724147 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43539 / 512000) (43547 / 512000) (3723911 / 1000000) (3724147 / 1000000) (265 / 8) (16567 / 500)
    (52911 / 1000) (53047 / 1000) (-111469 / 200) (93369 / 250000) (3077707 / 1000) (3600959 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3723911 / 1000000) (71092186971 / 1000000) (3600959 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3723911 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3723911 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell683 :
    ∀ t ∈ Set.Icc ((43547 / 512000) : ℝ) (8711 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((118542987 / 100000000) : ℝ) ≤ Real.exp (2 * (43547 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43547 / 512000)) (118542987 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8711 / 102400) : ℝ)) ≤ (296366729 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8711 / 102400)) (296366729 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4444808209 / 62500) : ℝ) ≤ Real.exp (3 * (3724027 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3724027 / 1000000)) (4444808209 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43547 / 512000) : ℝ) (8711 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3724027 / 1000000) (3724263 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43547 / 512000) (8711 / 102400) (118542987 / 100000000) (296366729 / 250000000) (3724027 / 1000000) (3724263 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43547 / 512000) (8711 / 102400) (3724027 / 1000000) (3724263 / 1000000) (33127 / 1000) (33137 / 1000)
    (26463 / 500) (53061 / 1000) (-139341 / 250) (373381 / 1000000) (3078091 / 1000) (1799853 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3724027 / 1000000) (4444808209 / 62500) (1799853 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3724027 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3724027 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell684 :
    ∀ t ∈ Set.Icc ((8711 / 102400) : ℝ) (43563 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((237093383 / 200000000) : ℝ) ≤ Real.exp (2 * (8711 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8711 / 102400)) (237093383 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43563 / 512000) : ℝ)) ≤ (1185503963 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43563 / 512000)) (1185503963 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((14228379551 / 200000) : ℝ) ≤ Real.exp (3 * (232759 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (232759 / 62500)) (14228379551 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8711 / 102400) : ℝ) (43563 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (232759 / 62500) (186219 / 50000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8711 / 102400) (43563 / 512000) (237093383 / 200000000) (1185503963 / 1000000000) (232759 / 62500) (186219 / 50000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8711 / 102400) (43563 / 512000) (232759 / 62500) (186219 / 50000) (3313 / 100) (1657 / 50)
    (2647 / 50) (13269 / 250) (-557383 / 1000) (74657 / 200000) (1539239 / 500) (3598443 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (232759 / 62500) (14228379551 / 200000) (3598443 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (232759 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (232759 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell685 :
    ∀ t ∈ Set.Icc ((43563 / 512000) : ℝ) (43571 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((592751981 / 500000000) : ℝ) ≤ Real.exp (2 * (43563 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43563 / 512000)) (592751981 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43571 / 512000) : ℝ)) ≤ (118554101 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43571 / 512000)) (118554101 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((71166659431 / 1000000) : ℝ) ≤ Real.exp (3 * (186213 / 50000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (186213 / 50000)) (71166659431 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43563 / 512000) : ℝ) (43571 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (186213 / 50000) (232781 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43563 / 512000) (43571 / 512000) (592751981 / 500000000) (118554101 / 100000000) (186213 / 50000) (232781 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43563 / 512000) (43571 / 512000) (186213 / 50000) (232781 / 62500) (33133 / 1000) (16571 / 500)
    (10591 / 200) (5309 / 100) (-557401 / 1000) (37319 / 100000) (3078861 / 1000) (3597191 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (186213 / 50000) (71166659431 / 1000000) (3597191 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (186213 / 50000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (186213 / 50000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell686 :
    ∀ t ∈ Set.Icc ((43571 / 512000) : ℝ) (43579 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1185541009 / 1000000000) : ℝ) ≤ Real.exp (2 * (43571 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43571 / 512000)) (1185541009 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43579 / 512000) : ℝ)) ≤ (1185578059 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43579 / 512000)) (1185578059 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((711916433 / 10000) : ℝ) ≤ Real.exp (3 * (3724377 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3724377 / 1000000)) (711916433 / 10000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43571 / 512000) : ℝ) (43579 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3724377 / 1000000) (3724613 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43571 / 512000) (43579 / 512000) (1185541009 / 1000000000) (1185578059 / 1000000000) (3724377 / 1000000) (3724613 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43571 / 512000) (43579 / 512000) (3724377 / 1000000) (3724613 / 1000000) (4142 / 125) (6629 / 200)
    (52969 / 1000) (10621 / 200) (-27871 / 50) (186547 / 500000) (384906 / 125) (449491 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3724377 / 1000000) (711916433 / 10000) (449491 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3724377 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3724377 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell687 :
    ∀ t ∈ Set.Icc ((43579 / 512000) : ℝ) (43587 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((592789029 / 500000000) : ℝ) ≤ Real.exp (2 * (43579 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43579 / 512000)) (592789029 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43587 / 512000) : ℝ)) ≤ (1185615109 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43587 / 512000)) (1185615109 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((7121642229 / 100000) : ℝ) ≤ Real.exp (3 * (3724493 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3724493 / 1000000)) (7121642229 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43579 / 512000) : ℝ) (43587 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3724493 / 1000000) (3724729 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43579 / 512000) (43587 / 512000) (592789029 / 500000000) (1185615109 / 1000000000) (3724493 / 1000000) (3724729 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43579 / 512000) (43587 / 512000) (3724493 / 1000000) (3724729 / 1000000) (33139 / 1000) (8287 / 250)
    (6623 / 125) (53119 / 1000) (-557439 / 1000) (372999 / 1000000) (384954 / 125) (3594677 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3724493 / 1000000) (7121642229 / 100000) (3594677 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3724493 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3724493 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell688 :
    ∀ t ∈ Set.Icc ((43587 / 512000) : ℝ) (8719 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((296403777 / 250000000) : ℝ) ≤ Real.exp (2 * (43587 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43587 / 512000)) (296403777 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8719 / 102400) : ℝ)) ≤ (3705163 / 3125000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8719 / 102400)) (3705163 / 3125000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4452575619 / 62500) : ℝ) ≤ Real.exp (3 * (3724609 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3724609 / 1000000)) (4452575619 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43587 / 512000) : ℝ) (8719 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3724609 / 1000000) (744969 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43587 / 512000) (8719 / 102400) (296403777 / 250000000) (3705163 / 3125000) (3724609 / 1000000) (744969 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43587 / 512000) (8719 / 102400) (3724609 / 1000000) (744969 / 200000) (33141 / 1000) (33151 / 1000)
    (26499 / 500) (26567 / 500) (-278729 / 500) (46613 / 125000) (616003 / 200) (1796713 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3724609 / 1000000) (4452575619 / 62500) (1796713 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3724609 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3724609 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell689 :
    ∀ t ∈ Set.Icc ((8719 / 102400) : ℝ) (43603 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1185652159 / 1000000000) : ℝ) ≤ Real.exp (2 * (8719 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8719 / 102400)) (1185652159 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43603 / 512000) : ℝ)) ≤ (296422303 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43603 / 512000)) (296422303 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8908277493 / 125000) : ℝ) ≤ Real.exp (3 * (1862363 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1862363 / 500000)) (8908277493 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8719 / 102400) : ℝ) (43603 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1862363 / 500000) (1862481 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8719 / 102400) (43603 / 512000) (1185652159 / 1000000000) (296422303 / 250000000) (1862363 / 500000) (1862481 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8719 / 102400) (43603 / 512000) (1862363 / 500000) (1862481 / 500000) (4143 / 125) (16577 / 500)
    (53013 / 1000) (13287 / 250) (-557477 / 1000) (372809 / 1000000) (1540201 / 500) (718433 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1862363 / 500000) (8908277493 / 125000) (718433 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1862363 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1862363 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell690 :
    ∀ t ∈ Set.Icc ((43603 / 512000) : ℝ) (43611 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1185689211 / 1000000000) : ℝ) ≤ Real.exp (2 * (43603 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43603 / 512000)) (1185689211 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43611 / 512000) : ℝ)) ≤ (592863133 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43611 / 512000)) (592863133 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((17822756223 / 250000) : ℝ) ≤ Real.exp (3 * (1862421 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1862421 / 500000)) (17822756223 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43603 / 512000) : ℝ) (43611 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1862421 / 500000) (1862539 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43603 / 512000) (43611 / 512000) (1185689211 / 1000000000) (592863133 / 500000000) (1862421 / 500000) (1862539 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43603 / 512000) (43611 / 512000) (1862421 / 500000) (1862539 / 500000) (33147 / 1000) (8289 / 250)
    (53027 / 1000) (53163 / 1000) (-69687 / 125) (186357 / 500000) (1540393 / 500) (718183 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1862421 / 500000) (17822756223 / 250000) (718183 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1862421 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1862421 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell691 :
    ∀ t ∈ Set.Icc ((43611 / 512000) : ℝ) (43619 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((237145253 / 200000000) : ℝ) ≤ Real.exp (2 * (43611 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43611 / 512000)) (237145253 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43619 / 512000) : ℝ)) ≤ (29644083 / 25000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43619 / 512000)) (29644083 / 25000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3565802621 / 50000) : ℝ) ≤ Real.exp (3 * (3724959 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3724959 / 1000000)) (3565802621 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43611 / 512000) : ℝ) (43619 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3724959 / 1000000) (745039 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43611 / 512000) (43619 / 512000) (237145253 / 200000000) (29644083 / 25000000) (3724959 / 1000000) (745039 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43611 / 512000) (43619 / 512000) (3724959 / 1000000) (745039 / 200000) (663 / 20) (33159 / 1000)
    (26521 / 500) (53177 / 1000) (-111503 / 200) (186309 / 500000) (3081173 / 1000) (717931 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3724959 / 1000000) (3565802621 / 50000) (717931 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3724959 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3724959 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell692 :
    ∀ t ∈ Set.Icc ((43619 / 512000) : ℝ) (8727 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1185763319 / 1000000000) : ℝ) ≤ Real.exp (2 * (43619 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43619 / 512000)) (1185763319 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8727 / 102400) : ℝ)) ≤ (1185837433 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8727 / 102400)) (1185837433 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8917609339 / 125000) : ℝ) ≤ Real.exp (3 * (149003 / 40000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (149003 / 40000)) (8917609339 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43619 / 512000) : ℝ) (8727 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (149003 / 40000) (3725427 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43619 / 512000) (8727 / 102400) (1185763319 / 1000000000) (1185837433 / 1000000000) (149003 / 40000) (3725427 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43619 / 512000) (8727 / 102400) (149003 / 40000) (3725427 / 1000000) (4144 / 125) (6633 / 200)
    (5303 / 100) (6654 / 125) (-557007 / 1000) (186279 / 500000) (3081941 / 1000) (1794203 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (149003 / 40000) (8917609339 / 125000) (1794203 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (149003 / 40000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (149003 / 40000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell693 :
    ∀ t ∈ Set.Icc ((8727 / 102400) : ℝ) (43651 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((148229679 / 125000000) : ℝ) ≤ Real.exp (2 * (8727 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8727 / 102400)) (148229679 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43651 / 512000) : ℝ)) ≤ (23718231 / 20000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43651 / 512000)) (23718231 / 20000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((71390759389 / 1000000) : ℝ) ≤ Real.exp (3 * (931327 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (931327 / 250000)) (71390759389 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8727 / 102400) : ℝ) (43651 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (931327 / 250000) (186283 / 50000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8727 / 102400) (43651 / 512000) (148229679 / 125000000) (23718231 / 20000000) (931327 / 250000) (186283 / 50000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8727 / 102400) (43651 / 512000) (931327 / 250000) (186283 / 50000) (33157 / 1000) (33171 / 1000)
    (53059 / 1000) (53261 / 1000) (-111409 / 200) (23273 / 62500) (385339 / 125) (3585899 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (931327 / 250000) (71390759389 / 1000000) (3585899 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (931327 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (931327 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell694 :
    ∀ t ∈ Set.Icc ((43651 / 512000) : ℝ) (43667 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1185911549 / 1000000000) : ℝ) ≤ Real.exp (2 * (43651 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43651 / 512000)) (1185911549 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43667 / 512000) : ℝ)) ≤ (148248209 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43667 / 512000)) (148248209 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((17860169737 / 250000) : ℝ) ≤ Real.exp (3 * (3725541 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3725541 / 1000000)) (17860169737 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43651 / 512000) : ℝ) (43667 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3725541 / 1000000) (3725893 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43651 / 512000) (43667 / 512000) (1185911549 / 1000000000) (148248209 / 125000000) (3725541 / 1000000) (3725893 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43651 / 512000) (43667 / 512000) (3725541 / 1000000) (3725893 / 1000000) (33163 / 1000) (4147 / 125)
    (6636 / 125) (5329 / 100) (-278541 / 500) (372177 / 1000000) (3083483 / 1000) (3583393 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3725541 / 1000000) (17860169737 / 250000) (3583393 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3725541 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3725541 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell695 :
    ∀ t ∈ Set.Icc ((43667 / 512000) : ℝ) (43683 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1185985671 / 1000000000) : ℝ) ≤ Real.exp (2 * (43667 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43667 / 512000)) (1185985671 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43683 / 512000) : ℝ)) ≤ (593029899 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43683 / 512000)) (593029899 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((35745209471 / 500000) : ℝ) ≤ Real.exp (3 * (3725773 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3725773 / 1000000)) (35745209471 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43667 / 512000) : ℝ) (43683 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3725773 / 1000000) (1863063 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43667 / 512000) (43683 / 512000) (1185985671 / 1000000000) (593029899 / 500000000) (3725773 / 1000000) (1863063 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43667 / 512000) (43683 / 512000) (3725773 / 1000000) (1863063 / 500000) (4146 / 125) (16591 / 500)
    (53117 / 1000) (1333 / 25) (-111423 / 200) (92997 / 250000) (1542127 / 500) (35809 / 10000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3725773 / 1000000) (35745209471 / 500000) (35809 / 10000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3725773 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3725773 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell696 :
    ∀ t ∈ Set.Icc ((43683 / 512000) : ℝ) (43699 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1186059797 / 1000000000) : ℝ) ≤ Real.exp (2 * (43683 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43683 / 512000)) (1186059797 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43699 / 512000) : ℝ)) ≤ (1186133929 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43699 / 512000)) (1186133929 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((71540408187 / 1000000) : ℝ) ≤ Real.exp (3 * (1863003 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1863003 / 500000)) (71540408187 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43683 / 512000) : ℝ) (43699 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1863003 / 500000) (3726359 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43683 / 512000) (43699 / 512000) (1186059797 / 1000000000) (1186133929 / 1000000000) (1863003 / 500000) (3726359 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43683 / 512000) (43699 / 512000) (1863003 / 500000) (3726359 / 1000000) (16587 / 500) (33187 / 1000)
    (26573 / 500) (53349 / 1000) (-69644 / 125) (185899 / 500000) (1542513 / 500) (1789199 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1863003 / 500000) (71540408187 / 1000000) (1789199 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1863003 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1863003 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell697 :
    ∀ t ∈ Set.Icc ((43699 / 512000) : ℝ) (8743 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((148266741 / 125000000) : ℝ) ≤ Real.exp (2 * (43699 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43699 / 512000)) (148266741 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8743 / 102400) : ℝ)) ≤ (237241613 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8743 / 102400)) (237241613 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((71590432387 / 1000000) : ℝ) ≤ Real.exp (3 * (3726239 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3726239 / 1000000)) (71590432387 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43699 / 512000) : ℝ) (8743 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3726239 / 1000000) (58228 / 15625) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43699 / 512000) (8743 / 102400) (148266741 / 125000000) (237241613 / 200000000) (3726239 / 1000000) (58228 / 15625) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43699 / 512000) (8743 / 102400) (3726239 / 1000000) (58228 / 15625) (33179 / 1000) (33193 / 1000)
    (2127 / 40) (26689 / 500) (-55719 / 100) (46451 / 125000) (1542899 / 500) (3575897 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3726239 / 1000000) (71590432387 / 1000000) (3575897 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3726239 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3726239 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell698 :
    ∀ t ∈ Set.Icc ((8743 / 102400) : ℝ) (43731 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((18534501 / 15625000) : ℝ) ≤ Real.exp (2 * (8743 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8743 / 102400)) (18534501 / 15625000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43731 / 512000) : ℝ)) ≤ (237256441 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43731 / 512000)) (237256441 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((35820245783 / 500000) : ℝ) ≤ Real.exp (3 * (465809 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (465809 / 125000)) (35820245783 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8743 / 102400) : ℝ) (43731 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (465809 / 125000) (149073 / 40000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8743 / 102400) (43731 / 512000) (18534501 / 15625000) (237256441 / 200000000) (465809 / 125000) (149073 / 40000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8743 / 102400) (43731 / 512000) (465809 / 125000) (149073 / 40000) (6637 / 200) (33199 / 1000)
    (13301 / 250) (53407 / 1000) (-557227 / 1000) (185709 / 500000) (3086569 / 1000) (3573399 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (465809 / 125000) (35820245783 / 500000) (3573399 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (465809 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (465809 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell699 :
    ∀ t ∈ Set.Icc ((43731 / 512000) : ℝ) (43747 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((296570551 / 250000000) : ℝ) ≤ Real.exp (2 * (43731 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43731 / 512000)) (296570551 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43747 / 512000) : ℝ)) ≤ (23727127 / 20000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43747 / 512000)) (23727127 / 20000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((17922646437 / 250000) : ℝ) ≤ Real.exp (3 * (745341 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (745341 / 200000)) (17922646437 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43731 / 512000) : ℝ) (43747 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (745341 / 200000) (1863529 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (43731 / 512000) (43747 / 512000) (296570551 / 250000000) (23727127 / 20000000) (745341 / 200000) (1863529 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (43731 / 512000) (43747 / 512000) (745341 / 200000) (1863529 / 500000) (3319 / 100) (8301 / 250)
    (53233 / 1000) (13359 / 250) (-111453 / 200) (92807 / 250000) (3087341 / 1000) (1785451 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (745341 / 200000) (17922646437 / 250000) (1785451 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (745341 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (745341 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch034 :
    ∀ t ∈ Set.Icc ((43523 / 512000) : ℝ) (43747 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell680
      hpThetaDensityLowerExpCompact_cell681)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell682
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell683
      hpThetaDensityLowerExpCompact_cell684)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell685
      hpThetaDensityLowerExpCompact_cell686)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell687
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell688
      hpThetaDensityLowerExpCompact_cell689))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell690
      hpThetaDensityLowerExpCompact_cell691)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell692
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell693
      hpThetaDensityLowerExpCompact_cell694)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell695
      hpThetaDensityLowerExpCompact_cell696)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell697
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell698
      hpThetaDensityLowerExpCompact_cell699)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch034
end HodgeProofHP
