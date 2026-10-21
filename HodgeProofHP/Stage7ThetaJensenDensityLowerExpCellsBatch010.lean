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
theorem hpThetaDensityLowerExpCompact_cell200 :
    ∀ t ∈ Set.Icc ((41207 / 512000) : ℝ) (41209 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((146830459 / 125000000) : ℝ) ≤ Real.exp (2 * (41207 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41207 / 512000)) (146830459 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41209 / 512000) : ℝ)) ≤ (1174652849 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41209 / 512000)) (1174652849 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6424304649 / 100000) : ℝ) ≤ Real.exp (3 * (3690143 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3690143 / 1000000)) (6424304649 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41207 / 512000) : ℝ) (41209 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3690143 / 1000000) (369029 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41207 / 512000) (41209 / 512000) (146830459 / 125000000) (1174652849 / 1000000000) (3690143 / 1000000) (369029 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41207 / 512000) (41209 / 512000) (3690143 / 1000000) (369029 / 100000) (16163 / 500) (32333 / 1000)
    (24399 / 500) (24441 / 500) (-551983 / 1000) (100531 / 250000) (370913 / 125) (996217 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3690143 / 1000000) (6424304649 / 100000) (996217 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3690143 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3690143 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell201 :
    ∀ t ∈ Set.Icc ((41209 / 512000) : ℝ) (41211 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((73415803 / 62500000) : ℝ) ≤ Real.exp (2 * (41209 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41209 / 512000)) (73415803 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41211 / 512000) : ℝ)) ≤ (587331013 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41211 / 512000)) (587331013 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6424844313 / 100000) : ℝ) ≤ Real.exp (3 * (3690171 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3690171 / 1000000)) (6424844313 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41209 / 512000) : ℝ) (41211 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3690171 / 1000000) (3690319 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41209 / 512000) (41211 / 512000) (73415803 / 62500000) (587331013 / 500000000) (3690171 / 1000000) (3690319 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41209 / 512000) (41211 / 512000) (3690171 / 1000000) (3690319 / 1000000) (32327 / 1000) (32333 / 1000)
    (24401 / 500) (24443 / 500) (-551983 / 1000) (402099 / 1000000) (2967397 / 1000) (3984533 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3690171 / 1000000) (6424844313 / 100000) (3984533 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3690171 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3690171 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell202 :
    ∀ t ∈ Set.Icc ((41211 / 512000) : ℝ) (41213 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((46986481 / 40000000) : ℝ) ≤ Real.exp (2 * (41211 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41211 / 512000)) (46986481 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41213 / 512000) : ℝ)) ≤ (293667801 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41213 / 512000)) (293667801 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((12850806597 / 200000) : ℝ) ≤ Real.exp (3 * (18451 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (18451 / 5000)) (12850806597 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41211 / 512000) : ℝ) (41213 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (18451 / 5000) (922587 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41211 / 512000) (41213 / 512000) (46986481 / 40000000) (293667801 / 250000000) (18451 / 5000) (922587 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41211 / 512000) (41213 / 512000) (18451 / 5000) (922587 / 250000) (4041 / 125) (16167 / 500)
    (9761 / 200) (48889 / 1000) (-551989 / 1000) (201037 / 500000) (2967491 / 1000) (1992093 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (18451 / 5000) (12850806597 / 200000) (1992093 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (18451 / 5000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (18451 / 5000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell203 :
    ∀ t ∈ Set.Icc ((41213 / 512000) : ℝ) (8243 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174671203 / 1000000000) : ℝ) ≤ Real.exp (2 * (41213 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41213 / 512000)) (1174671203 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8243 / 102400) : ℝ)) ≤ (1174680381 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8243 / 102400)) (1174680381 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64259623327 / 1000000) : ℝ) ≤ Real.exp (3 * (3690229 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3690229 / 1000000)) (64259623327 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41213 / 512000) : ℝ) (8243 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3690229 / 1000000) (461297 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41213 / 512000) (8243 / 102400) (1174671203 / 1000000000) (1174680381 / 1000000000) (3690229 / 1000000) (461297 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41213 / 512000) (8243 / 102400) (3690229 / 1000000) (461297 / 125000) (4041 / 125) (6467 / 200)
    (48809 / 1000) (48893 / 1000) (-275999 / 500) (6282 / 15625) (2967581 / 1000) (24899 / 6250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3690229 / 1000000) (64259623327 / 1000000) (24899 / 6250000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3690229 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3690229 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell204 :
    ∀ t ∈ Set.Icc ((8243 / 102400) : ℝ) (41217 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((58734019 / 50000000) : ℝ) ≤ Real.exp (2 * (8243 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8243 / 102400)) (58734019 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41217 / 512000) : ℝ)) ≤ (587344779 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41217 / 512000)) (587344779 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32132607077 / 500000) : ℝ) ≤ Real.exp (3 * (1845129 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1845129 / 500000)) (32132607077 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8243 / 102400) : ℝ) (41217 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1845129 / 500000) (738081 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8243 / 102400) (41217 / 512000) (58734019 / 50000000) (587344779 / 500000000) (1845129 / 500000) (738081 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8243 / 102400) (41217 / 512000) (1845129 / 500000) (738081 / 200000) (32329 / 1000) (6467 / 200)
    (12203 / 250) (6112 / 125) (-552003 / 1000) (402023 / 1000000) (1483837 / 500) (3983493 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1845129 / 500000) (32132607077 / 500000) (3983493 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1845129 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1845129 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell205 :
    ∀ t ∈ Set.Icc ((41217 / 512000) : ℝ) (41219 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174689557 / 1000000000) : ℝ) ≤ Real.exp (2 * (41217 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41217 / 512000)) (1174689557 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41219 / 512000) : ℝ)) ≤ (234939747 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41219 / 512000)) (234939747 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64270805469 / 1000000) : ℝ) ≤ Real.exp (3 * (3690287 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3690287 / 1000000)) (64270805469 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41217 / 512000) : ℝ) (41219 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3690287 / 1000000) (1845217 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41217 / 512000) (41219 / 512000) (1174689557 / 1000000000) (234939747 / 200000000) (3690287 / 1000000) (1845217 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41217 / 512000) (41219 / 512000) (3690287 / 1000000) (1845217 / 500000) (3233 / 100) (4042 / 125)
    (6102 / 125) (489 / 10) (-552009 / 1000) (401997 / 1000000) (2967767 / 1000) (1991573 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3690287 / 1000000) (64270805469 / 1000000) (1991573 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3690287 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3690287 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell206 :
    ∀ t ∈ Set.Icc ((41219 / 512000) : ℝ) (41221 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587349367 / 500000000) : ℝ) ≤ Real.exp (2 * (41219 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41219 / 512000)) (587349367 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41221 / 512000) : ℝ)) ≤ (1174707913 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41221 / 512000)) (1174707913 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6427639727 / 100000) : ℝ) ≤ Real.exp (3 * (922579 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (922579 / 250000)) (6427639727 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41219 / 512000) : ℝ) (41221 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (922579 / 250000) (3690463 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41219 / 512000) (41221 / 512000) (587349367 / 500000000) (1174707913 / 1000000000) (922579 / 250000) (3690463 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41219 / 512000) (41221 / 512000) (922579 / 250000) (3690463 / 1000000) (3233 / 100) (32337 / 1000)
    (48819 / 1000) (48903 / 1000) (-276007 / 500) (100493 / 250000) (148393 / 50) (9957 / 2500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (922579 / 250000) (6427639727 / 100000) (9957 / 2500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922579 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922579 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell207 :
    ∀ t ∈ Set.Icc ((41221 / 512000) : ℝ) (41223 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((146838489 / 125000000) : ℝ) ≤ Real.exp (2 * (41221 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41221 / 512000)) (146838489 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41223 / 512000) : ℝ)) ≤ (117471709 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41223 / 512000)) (117471709 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64281796711 / 1000000) : ℝ) ≤ Real.exp (3 * (461293 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (461293 / 125000)) (64281796711 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41221 / 512000) : ℝ) (41223 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (461293 / 125000) (922623 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41221 / 512000) (41223 / 512000) (146838489 / 125000000) (117471709 / 100000000) (461293 / 125000) (922623 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41221 / 512000) (41223 / 512000) (461293 / 125000) (922623 / 250000) (32331 / 1000) (32337 / 1000)
    (24411 / 500) (48907 / 1000) (-276007 / 500) (401947 / 1000000) (1483977 / 500) (796493 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (461293 / 125000) (64281796711 / 1000000) (796493 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461293 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (461293 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell208 :
    ∀ t ∈ Set.Icc ((41223 / 512000) : ℝ) (1649 / 20480), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174717089 / 1000000000) : ℝ) ≤ Real.exp (2 * (41223 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41223 / 512000)) (1174717089 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1649 / 20480) : ℝ)) ≤ (293681567 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1649 / 20480)) (293681567 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64287389469 / 1000000) : ℝ) ≤ Real.exp (3 * (3690373 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3690373 / 1000000)) (64287389469 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41223 / 512000) : ℝ) (1649 / 20480),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3690373 / 1000000) (3690521 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41223 / 512000) (1649 / 20480) (1174717089 / 1000000000) (293681567 / 250000000) (3690373 / 1000000) (3690521 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41223 / 512000) (1649 / 20480) (3690373 / 1000000) (3690521 / 1000000) (8083 / 250) (16169 / 500)
    (24413 / 500) (4891 / 100) (-552019 / 1000) (200961 / 500000) (2968047 / 1000) (3982119 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3690373 / 1000000) (64287389469 / 1000000) (3982119 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3690373 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3690373 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell209 :
    ∀ t ∈ Set.Icc ((1649 / 20480) : ℝ) (41227 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174726267 / 1000000000) : ℝ) ≤ Real.exp (2 * (1649 / 20480)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1649 / 20480)) (1174726267 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41227 / 512000) : ℝ)) ≤ (234947089 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41227 / 512000)) (234947089 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8036622839 / 125000) : ℝ) ≤ Real.exp (3 * (1845201 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1845201 / 500000)) (8036622839 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1649 / 20480) : ℝ) (41227 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1845201 / 500000) (3690549 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1649 / 20480) (41227 / 512000) (1174726267 / 1000000000) (234947089 / 200000000) (1845201 / 500000) (3690549 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1649 / 20480) (41227 / 512000) (1845201 / 500000) (3690549 / 1000000) (8083 / 250) (32339 / 1000)
    (4883 / 100) (48913 / 1000) (-552029 / 1000) (50237 / 125000) (2968137 / 1000) (3981773 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1845201 / 500000) (8036622839 / 125000) (3981773 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1845201 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1845201 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell210 :
    ∀ t ∈ Set.Icc ((41227 / 512000) : ℝ) (41229 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((293683861 / 250000000) : ℝ) ≤ Real.exp (2 * (41227 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41227 / 512000)) (293683861 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41229 / 512000) : ℝ)) ≤ (1174744623 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41229 / 512000)) (1174744623 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64298576443 / 1000000) : ℝ) ≤ Real.exp (3 * (3690431 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3690431 / 1000000)) (64298576443 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41227 / 512000) : ℝ) (41229 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3690431 / 1000000) (1845289 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41227 / 512000) (41229 / 512000) (293683861 / 250000000) (1174744623 / 1000000000) (3690431 / 1000000) (1845289 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41227 / 512000) (41229 / 512000) (3690431 / 1000000) (1845289 / 500000) (32333 / 1000) (32339 / 1000)
    (48833 / 1000) (48917 / 1000) (-276017 / 500) (40187 / 100000) (296823 / 100) (1990713 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3690431 / 1000000) (64298576443 / 1000000) (1990713 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3690431 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3690431 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell211 :
    ∀ t ∈ Set.Icc ((41229 / 512000) : ℝ) (41231 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587372311 / 500000000) : ℝ) ≤ Real.exp (2 * (41229 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41229 / 512000)) (587372311 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41231 / 512000) : ℝ)) ≤ (1174753801 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41231 / 512000)) (1174753801 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3215208533 / 50000) : ℝ) ≤ Real.exp (3 * (184523 / 50000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (184523 / 50000)) (3215208533 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41229 / 512000) : ℝ) (41231 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (184523 / 50000) (3690607 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41229 / 512000) (41231 / 512000) (587372311 / 500000000) (1174753801 / 1000000000) (184523 / 50000) (3690607 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41229 / 512000) (41231 / 512000) (184523 / 50000) (3690607 / 1000000) (16167 / 500) (1617 / 50)
    (48837 / 1000) (1223 / 25) (-552039 / 1000) (80369 / 200000) (742081 / 250) (99527 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (184523 / 50000) (3215208533 / 50000) (99527 / 25000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (184523 / 50000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (184523 / 50000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell212 :
    ∀ t ∈ Set.Icc ((41231 / 512000) : ℝ) (41233 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((5873769 / 5000000) : ℝ) ≤ Real.exp (2 * (41231 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41231 / 512000)) (5873769 / 5000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41233 / 512000) : ℝ)) ≤ (587381489 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41233 / 512000)) (587381489 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64309765363 / 1000000) : ℝ) ≤ Real.exp (3 * (3690489 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3690489 / 1000000)) (64309765363 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41231 / 512000) : ℝ) (41233 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3690489 / 1000000) (922659 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41231 / 512000) (41233 / 512000) (5873769 / 5000000) (587381489 / 500000000) (3690489 / 1000000) (922659 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41231 / 512000) (41233 / 512000) (3690489 / 1000000) (922659 / 250000) (6467 / 200) (32341 / 1000)
    (1221 / 25) (12231 / 250) (-110409 / 200) (401819 / 1000000) (2968417 / 1000) (3980733 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3690489 / 1000000) (64309765363 / 1000000) (3980733 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3690489 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3690489 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell213 :
    ∀ t ∈ Set.Icc ((41233 / 512000) : ℝ) (8247 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174762977 / 1000000000) : ℝ) ≤ Real.exp (2 * (41233 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41233 / 512000)) (1174762977 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8247 / 102400) : ℝ)) ≤ (293693039 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8247 / 102400)) (293693039 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8039395951 / 125000) : ℝ) ≤ Real.exp (3 * (3690517 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3690517 / 1000000)) (8039395951 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41233 / 512000) : ℝ) (8247 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3690517 / 1000000) (738133 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41233 / 512000) (8247 / 102400) (1174762977 / 1000000000) (293693039 / 250000000) (3690517 / 1000000) (738133 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41233 / 512000) (8247 / 102400) (3690517 / 1000000) (738133 / 200000) (6467 / 200) (32341 / 1000)
    (48843 / 1000) (6116 / 125) (-110409 / 200) (80359 / 200000) (296851 / 100) (3980399 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3690517 / 1000000) (8039395951 / 125000) (3980399 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3690517 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3690517 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell214 :
    ∀ t ∈ Set.Icc ((8247 / 102400) : ℝ) (41237 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((234954431 / 200000000) : ℝ) ≤ Real.exp (2 * (8247 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8247 / 102400)) (234954431 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41237 / 512000) : ℝ)) ≤ (587390667 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41237 / 512000)) (587390667 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64320763269 / 1000000) : ℝ) ≤ Real.exp (3 * (1845273 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1845273 / 500000)) (64320763269 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8247 / 102400) : ℝ) (41237 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1845273 / 500000) (1845347 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8247 / 102400) (41237 / 512000) (234954431 / 200000000) (587390667 / 500000000) (1845273 / 500000) (1845347 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8247 / 102400) (41237 / 512000) (1845273 / 500000) (1845347 / 500000) (4042 / 125) (16171 / 500)
    (48847 / 1000) (48931 / 1000) (-11041 / 20) (40177 / 100000) (742151 / 250) (3980053 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1845273 / 500000) (64320763269 / 1000000) (3980053 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1845273 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1845273 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell215 :
    ∀ t ∈ Set.Icc ((41237 / 512000) : ℝ) (41239 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174781333 / 1000000000) : ℝ) ≤ Real.exp (2 * (41237 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41237 / 512000)) (1174781333 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41239 / 512000) : ℝ)) ≤ (73424407 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41239 / 512000)) (73424407 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8040794927 / 125000) : ℝ) ≤ Real.exp (3 * (147623 / 40000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (147623 / 40000)) (8040794927 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41237 / 512000) : ℝ) (41239 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (147623 / 40000) (1845361 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41237 / 512000) (41239 / 512000) (1174781333 / 1000000000) (73424407 / 62500000) (147623 / 40000) (1845361 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41237 / 512000) (41239 / 512000) (147623 / 40000) (1845361 / 500000) (32337 / 1000) (32343 / 1000)
    (977 / 20) (24467 / 500) (-27603 / 50) (25109 / 62500) (1484347 / 500) (3979707 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (147623 / 40000) (8040794927 / 125000) (3979707 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (147623 / 40000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (147623 / 40000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell216 :
    ∀ t ∈ Set.Icc ((41239 / 512000) : ℝ) (41241 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174790511 / 1000000000) : ℝ) ≤ Real.exp (2 * (41239 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41239 / 512000)) (1174790511 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41241 / 512000) : ℝ)) ≤ (117479969 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41241 / 512000)) (117479969 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1286639121 / 20000) : ℝ) ≤ Real.exp (3 * (922651 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (922651 / 250000)) (1286639121 / 20000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41239 / 512000) : ℝ) (41241 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (922651 / 250000) (3690751 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41239 / 512000) (41241 / 512000) (1174790511 / 1000000000) (117479969 / 100000000) (922651 / 250000) (3690751 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41239 / 512000) (41241 / 512000) (922651 / 250000) (3690751 / 1000000) (32337 / 1000) (32343 / 1000)
    (24427 / 500) (24469 / 500) (-110413 / 200) (200859 / 500000) (2968787 / 1000) (24871 / 6250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (922651 / 250000) (1286639121 / 20000) (24871 / 6250000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922651 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922651 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell217 :
    ∀ t ∈ Set.Icc ((41241 / 512000) : ℝ) (41243 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174799689 / 1000000000) : ℝ) ≤ Real.exp (2 * (41241 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41241 / 512000)) (1174799689 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41243 / 512000) : ℝ)) ≤ (293702217 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41243 / 512000)) (293702217 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64337553171 / 1000000) : ℝ) ≤ Real.exp (3 * (3690633 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3690633 / 1000000)) (64337553171 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41241 / 512000) : ℝ) (41243 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3690633 / 1000000) (184539 / 50000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41241 / 512000) (41243 / 512000) (1174799689 / 1000000000) (293702217 / 250000000) (3690633 / 1000000) (184539 / 50000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41241 / 512000) (41243 / 512000) (3690633 / 1000000) (184539 / 50000) (16169 / 500) (4043 / 125)
    (48857 / 1000) (48941 / 1000) (-55207 / 100) (401693 / 1000000) (74222 / 25) (1989507 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3690633 / 1000000) (64337553171 / 1000000) (1989507 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3690633 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3690633 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell218 :
    ∀ t ∈ Set.Icc ((41243 / 512000) : ℝ) (8249 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174808867 / 1000000000) : ℝ) ≤ Real.exp (2 * (41243 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41243 / 512000)) (1174808867 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8249 / 102400) : ℝ)) ≤ (1174818047 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8249 / 102400)) (1174818047 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3217157539 / 50000) : ℝ) ≤ Real.exp (3 * (1845331 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1845331 / 500000)) (3217157539 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41243 / 512000) : ℝ) (8249 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1845331 / 500000) (3690809 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41243 / 512000) (8249 / 102400) (1174808867 / 1000000000) (1174818047 / 1000000000) (1845331 / 500000) (3690809 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41243 / 512000) (8249 / 102400) (1845331 / 500000) (3690809 / 1000000) (32339 / 1000) (6469 / 200)
    (48861 / 1000) (9789 / 200) (-22083 / 40) (401667 / 1000000) (1484487 / 500) (994667 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1845331 / 500000) (3217157539 / 50000) (994667 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1845331 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1845331 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell219 :
    ∀ t ∈ Set.Icc ((8249 / 102400) : ℝ) (41247 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587409023 / 500000000) : ℝ) ≤ Real.exp (2 * (8249 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8249 / 102400)) (587409023 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41247 / 512000) : ℝ)) ≤ (46993089 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41247 / 512000)) (46993089 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64348555829 / 1000000) : ℝ) ≤ Real.exp (3 * (369069 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (369069 / 100000)) (64348555829 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8249 / 102400) : ℝ) (41247 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (369069 / 100000) (1845419 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8249 / 102400) (41247 / 512000) (587409023 / 500000000) (46993089 / 40000000) (369069 / 100000) (1845419 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8249 / 102400) (41247 / 512000) (369069 / 100000) (1845419 / 500000) (32339 / 1000) (16173 / 500)
    (6108 / 125) (12237 / 250) (-138019 / 250) (401643 / 1000000) (2969067 / 1000) (1989167 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (369069 / 100000) (64348555829 / 1000000) (1989167 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (369069 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (369069 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch010 :
    ∀ t ∈ Set.Icc ((41207 / 512000) : ℝ) (41247 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell200
      hpThetaDensityLowerExpCompact_cell201)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell202
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell203
      hpThetaDensityLowerExpCompact_cell204)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell205
      hpThetaDensityLowerExpCompact_cell206)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell207
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell208
      hpThetaDensityLowerExpCompact_cell209))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell210
      hpThetaDensityLowerExpCompact_cell211)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell212
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell213
      hpThetaDensityLowerExpCompact_cell214)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell215
      hpThetaDensityLowerExpCompact_cell216)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell217
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell218
      hpThetaDensityLowerExpCompact_cell219)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch010
end HodgeProofHP
