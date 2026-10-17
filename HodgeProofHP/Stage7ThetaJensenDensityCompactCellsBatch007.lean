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
theorem hpThetaDensityCompact_cell140 :
    ∀ t ∈ Set.Icc ((77 / 400) : ℝ) (193 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1469614321 / 1000000000) : ℝ) ≤ Real.exp (2 * (77 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (77 / 400)) (1469614321 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((193 / 1000) : ℝ)) ≤ (1471084671 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (193 / 1000)) (1471084671 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((41418469981 / 40000) : ℝ) ≤ Real.exp (3 * (4616793 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4616793 / 1000000)) (41418469981 / 40000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((77 / 400) : ℝ) (193 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4616793 / 1000000) (115539 / 25000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (77 / 400) (193 / 1000) (1469614321 / 1000000000) (1471084671 / 1000000000) (4616793 / 1000000) (115539 / 25000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (77 / 400) (193 / 1000) (4616793 / 1000000) (115539 / 25000) (57529 / 1000) (11547 / 200)
    (107867 / 500) (219569 / 1000) (-185601 / 500) (3159 / 1000) (1459837 / 200) (247233 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4616793 / 1000000) (41418469981 / 40000) (247233 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4616793 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4616793 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell141 :
    ∀ t ∈ Set.Icc ((193 / 1000) : ℝ) (387 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((147108467 / 100000000) : ℝ) ≤ Real.exp (2 * (193 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (193 / 1000)) (147108467 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((387 / 2000) : ℝ)) ≤ (368139123 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (387 / 2000)) (368139123 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((524954799053 / 500000) : ℝ) ≤ Real.exp (3 * (1155353 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1155353 / 250000)) (524954799053 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((193 / 1000) : ℝ) (387 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1155353 / 250000) (578273 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (193 / 1000) (387 / 2000) (147108467 / 100000000) (368139123 / 250000000) (1155353 / 250000) (578273 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (193 / 1000) (387 / 2000) (1155353 / 250000) (578273 / 125000) (7209 / 125) (28939 / 500)
    (108443 / 500) (220731 / 1000) (-368177 / 1000) (3169 / 1000) (7328441 / 1000) (243831 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1155353 / 250000) (524954799053 / 500000) (243831 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1155353 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1155353 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell142 :
    ∀ t ∈ Set.Icc ((387 / 2000) : ℝ) (97 / 500), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1472556491 / 1000000000) : ℝ) ≤ Real.exp (2 * (387 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (387 / 2000)) (1472556491 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((97 / 500) : ℝ)) ≤ (294805957 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (97 / 500)) (294805957 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((106457499893 / 100000) : ℝ) ≤ Real.exp (3 * (1156509 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1156509 / 250000)) (106457499893 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((387 / 2000) : ℝ) (97 / 500),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1156509 / 250000) (1157703 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (387 / 2000) (97 / 500) (1472556491 / 1000000000) (294805957 / 200000000) (1156509 / 250000) (1157703 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (387 / 2000) (97 / 500) (1156509 / 250000) (1157703 / 250000) (11563 / 200) (29011 / 500)
    (218043 / 1000) (221897 / 1000) (-45641 / 125) (1589 / 500) (7357811 / 1000) (30059 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1156509 / 250000) (106457499893 / 100000) (30059 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1156509 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1156509 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell143 :
    ∀ t ∈ Set.Icc ((97 / 500) : ℝ) (389 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((184253723 / 125000000) : ℝ) ≤ Real.exp (2 * (97 / 500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (97 / 500)) (184253723 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((389 / 2000) : ℝ)) ≤ (184438069 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (389 / 2000)) (184438069 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1079458195221 / 1000000) : ℝ) ≤ Real.exp (3 * (578833 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (578833 / 125000)) (1079458195221 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((97 / 500) : ℝ) (389 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (578833 / 125000) (2317723 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (97 / 500) (389 / 2000) (184253723 / 125000000) (184438069 / 125000000) (578833 / 125000) (2317723 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (97 / 500) (389 / 2000) (578833 / 125000) (2317723 / 500000) (57959 / 1000) (29083 / 500)
    (219203 / 1000) (223069 / 1000) (-362031 / 1000) (797 / 250) (3693653 / 500) (237157 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (578833 / 125000) (1079458195221 / 1000000) (237157 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (578833 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (578833 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell144 :
    ∀ t ∈ Set.Icc ((389 / 2000) : ℝ) (39 / 200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1475504551 / 1000000000) : ℝ) ≤ Real.exp (2 * (389 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (389 / 2000)) (1475504551 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((39 / 200) : ℝ)) ≤ (738490397 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (39 / 200)) (738490397 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((54728293739 / 50000) : ℝ) ≤ Real.exp (3 * (4635297 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4635297 / 1000000)) (54728293739 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((389 / 2000) : ℝ) (39 / 200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4635297 / 1000000) (4640083 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (389 / 2000) (39 / 200) (1475504551 / 1000000000) (738490397 / 500000000) (4635297 / 1000000) (4640083 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (389 / 2000) (39 / 200) (4635297 / 1000000) (4640083 / 1000000) (58103 / 1000) (5831 / 100)
    (220369 / 1000) (56061 / 250) (-179459 / 500) (3197 / 1000) (741691 / 100) (233883 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4635297 / 1000000) (54728293739 / 50000) (233883 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4635297 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4635297 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell145 :
    ∀ t ∈ Set.Icc ((39 / 200) : ℝ) (391 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1476980793 / 1000000000) : ℝ) ≤ Real.exp (2 * (39 / 200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (39 / 200)) (1476980793 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((391 / 2000) : ℝ)) ≤ (739229257 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (391 / 2000)) (739229257 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((277475408853 / 250000) : ℝ) ≤ Real.exp (3 * (927987 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (927987 / 200000)) (277475408853 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((39 / 200) : ℝ) (391 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (927987 / 200000) (2322363 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (39 / 200) (391 / 2000) (1476980793 / 1000000000) (739229257 / 500000000) (927987 / 200000) (2322363 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (39 / 200) (391 / 2000) (927987 / 200000) (2322363 / 500000) (58247 / 1000) (11691 / 200)
    (221539 / 1000) (9017 / 40) (-71153 / 200) (3207 / 1000) (7446641 / 1000) (57663 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (927987 / 200000) (277475408853 / 250000) (57663 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (927987 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (927987 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell146 :
    ∀ t ∈ Set.Icc ((391 / 2000) : ℝ) (49 / 250), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1478458513 / 1000000000) : ℝ) ≤ Real.exp (2 * (391 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (391 / 2000)) (1478458513 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((49 / 250) : ℝ)) ≤ (92496107 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (49 / 250)) (92496107 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((562732879667 / 500000) : ℝ) ≤ Real.exp (3 * (4644577 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4644577 / 1000000)) (562732879667 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((391 / 2000) : ℝ) (49 / 250),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4644577 / 1000000) (4649373 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (391 / 2000) (49 / 250) (1478458513 / 1000000000) (92496107 / 62500000) (4644577 / 1000000) (4649373 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (391 / 2000) (49 / 250) (4644577 / 1000000) (4649373 / 1000000) (7299 / 125) (293 / 5)
    (111357 / 500) (22661 / 100) (-352579 / 1000) (3217 / 1000) (7476487 / 1000) (113731 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4644577 / 1000000) (562732879667 / 500000) (113731 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4644577 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4644577 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell147 :
    ∀ t ∈ Set.Icc ((49 / 250) : ℝ) (393 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1479937711 / 1000000000) : ℝ) ≤ Real.exp (2 * (49 / 250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (49 / 250)) (1479937711 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((393 / 2000) : ℝ)) ≤ (148141839 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (393 / 2000)) (148141839 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1141265248323 / 1000000) : ℝ) ≤ Real.exp (3 * (581153 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (581153 / 125000)) (1141265248323 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((49 / 250) : ℝ) (393 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (581153 / 125000) (186161 / 40000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (49 / 250) (393 / 2000) (1479937711 / 1000000000) (148141839 / 100000000) (581153 / 125000) (186161 / 40000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (49 / 250) (393 / 2000) (581153 / 125000) (186161 / 40000) (7317 / 125) (11749 / 200)
    (111947 / 500) (1139 / 5) (-349361 / 1000) (1613 / 500) (1501291 / 200) (224313 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (581153 / 125000) (1141265248323 / 1000000) (224313 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (581153 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (581153 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell148 :
    ∀ t ∈ Set.Icc ((393 / 2000) : ℝ) (197 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1481418389 / 1000000000) : ℝ) ≤ Real.exp (2 * (393 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (393 / 2000)) (1481418389 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((197 / 1000) : ℝ)) ≤ (1482900549 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (197 / 1000)) (1482900549 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((578650205791 / 500000) : ℝ) ≤ Real.exp (3 * (37231 / 8000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (37231 / 8000)) (578650205791 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((393 / 2000) : ℝ) (197 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (37231 / 8000) (4658681 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (393 / 2000) (197 / 1000) (1481418389 / 1000000000) (1482900549 / 1000000000) (37231 / 8000) (4658681 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (393 / 2000) (197 / 1000) (37231 / 8000) (4658681 / 1000000) (29341 / 500) (5889 / 100)
    (112539 / 500) (114497 / 500) (-34611 / 100) (809 / 250) (3768269 / 500) (44241 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (37231 / 8000) (578650205791 / 500000) (44241 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (37231 / 8000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (37231 / 8000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell149 :
    ∀ t ∈ Set.Icc ((197 / 1000) : ℝ) (79 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((370725137 / 250000000) : ℝ) ≤ Real.exp (2 * (197 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (197 / 1000)) (370725137 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((79 / 400) : ℝ)) ≤ (1484384191 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (79 / 400)) (1484384191 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1173581988781 / 1000000) : ℝ) ≤ Real.exp (3 * (1164633 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1164633 / 250000)) (1173581988781 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((197 / 1000) : ℝ) (79 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1164633 / 250000) (2331671 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (197 / 1000) (79 / 400) (370725137 / 250000000) (1484384191 / 1000000000) (1164633 / 250000) (2331671 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (197 / 1000) (79 / 400) (1164633 / 250000) (2331671 / 500000) (58827 / 1000) (14759 / 250)
    (226267 / 1000) (115097 / 500) (-342833 / 1000) (1623 / 500) (1513349 / 200) (27267 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1164633 / 250000) (1173581988781 / 1000000) (27267 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1164633 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1164633 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell150 :
    ∀ t ∈ Set.Icc ((79 / 400) : ℝ) (99 / 500), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((148438419 / 100000000) : ℝ) ≤ Real.exp (2 * (79 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (79 / 400)) (148438419 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((99 / 500) : ℝ)) ≤ (742934659 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (99 / 500)) (742934659 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1190103325811 / 1000000) : ℝ) ≤ Real.exp (3 * (582899 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (582899 / 125000)) (1190103325811 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((79 / 400) : ℝ) (99 / 500),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (582899 / 125000) (583501 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (79 / 400) (99 / 500) (148438419 / 100000000) (742934659 / 500000000) (582899 / 125000) (583501 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (79 / 400) (99 / 500) (582899 / 125000) (583501 / 125000) (58973 / 1000) (59183 / 1000)
    (227461 / 1000) (115699 / 500) (-84877 / 250) (651 / 200) (3798537 / 500) (53777 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (582899 / 125000) (1190103325811 / 1000000) (53777 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (582899 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (582899 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell151 :
    ∀ t ∈ Set.Icc ((99 / 500) : ℝ) (397 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1485869317 / 1000000000) : ℝ) ≤ Real.exp (2 * (99 / 500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (99 / 500)) (1485869317 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((397 / 2000) : ℝ)) ≤ (1487355931 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (397 / 2000)) (1487355931 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1206878958469 / 1000000) : ℝ) ≤ Real.exp (3 * (2333929 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2333929 / 500000)) (1206878958469 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((99 / 500) : ℝ) (397 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2333929 / 500000) (2336339 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (99 / 500) (397 / 2000) (1485869317 / 1000000000) (1487355931 / 1000000000) (2333929 / 500000) (2336339 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (99 / 500) (397 / 2000) (2333929 / 500000) (2336339 / 500000) (59119 / 1000) (59329 / 1000)
    (11433 / 50) (232607 / 1000) (-67233 / 200) (653 / 200) (7627521 / 1000) (106059 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2333929 / 500000) (1206878958469 / 1000000) (106059 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2333929 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2333929 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell152 :
    ∀ t ∈ Set.Icc ((397 / 2000) : ℝ) (199 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((148735593 / 100000000) : ℝ) ≤ Real.exp (2 * (397 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (397 / 2000)) (148735593 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((199 / 1000) : ℝ)) ≤ (148884403 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (199 / 1000)) (148884403 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((611952867897 / 500000) : ℝ) ≤ Real.exp (3 * (292033 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (292033 / 62500)) (611952867897 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((397 / 2000) : ℝ) (199 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (292033 / 62500) (4677353 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (397 / 2000) (199 / 1000) (148735593 / 100000000) (148884403 / 100000000) (292033 / 62500) (4677353 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (397 / 2000) (199 / 1000) (292033 / 62500) (4677353 / 1000000) (11853 / 200) (14869 / 250)
    (229863 / 1000) (11691 / 50) (-16639 / 50) (131 / 40) (1914523 / 250) (209167 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (292033 / 62500) (611952867897 / 500000) (209167 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (292033 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (292033 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell153 :
    ∀ t ∈ Set.Icc ((199 / 1000) : ℝ) (399 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1488844029 / 1000000000) : ℝ) ≤ Real.exp (2 * (199 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (199 / 1000)) (1488844029 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((399 / 2000) : ℝ)) ≤ (1490333619 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (399 / 2000)) (1490333619 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((24823826709 / 20000) : ℝ) ≤ Real.exp (3 * (4677203 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4677203 / 1000000)) (24823826709 / 20000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((199 / 1000) : ℝ) (399 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4677203 / 1000000) (4682033 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (199 / 1000) (399 / 2000) (1488844029 / 1000000000) (1490333619 / 1000000000) (4677203 / 1000000) (4682033 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (199 / 1000) (399 / 2000) (4677203 / 1000000) (4682033 / 1000000) (14853 / 250) (59623 / 1000)
    (231071 / 1000) (235039 / 1000) (-329361 / 1000) (657 / 200) (1922197 / 250) (103127 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4677203 / 1000000) (24823826709 / 20000) (103127 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4677203 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4677203 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell154 :
    ∀ t ∈ Set.Icc ((399 / 2000) : ℝ) (1 / 5), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((745166809 / 500000000) : ℝ) ≤ Real.exp (2 * (399 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (399 / 2000)) (745166809 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1 / 5) : ℝ)) ≤ (745912349 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1 / 5)) (745912349 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((314684983649 / 250000) : ℝ) ≤ Real.exp (3 * (4681883 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4681883 / 1000000)) (314684983649 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((399 / 2000) : ℝ) (1 / 5),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4681883 / 1000000) (4686717 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (399 / 2000) (1 / 5) (745166809 / 500000000) (745912349 / 500000000) (4681883 / 1000000) (4686717 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (399 / 2000) (1 / 5) (4681883 / 1000000) (4686717 / 1000000) (59559 / 1000) (5977 / 100)
    (58071 / 250) (118131 / 500) (-81479 / 250) (659 / 200) (3859801 / 500) (101689 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4681883 / 1000000) (314684983649 / 250000) (101689 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4681883 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4681883 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityCompact_cellsBatch007 :
    ∀ t ∈ Set.Icc ((77 / 400) : ℝ) (1 / 5),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell140
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell141
      hpThetaDensityCompact_cell142))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell143
      hpThetaDensityCompact_cell144)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell145
      hpThetaDensityCompact_cell146)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell147
      hpThetaDensityCompact_cell148)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell149
      hpThetaDensityCompact_cell150))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell151
      hpThetaDensityCompact_cell152)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell153
      hpThetaDensityCompact_cell154))))

#print axioms hpThetaDensityCompact_cellsBatch007
end HodgeProofHP
