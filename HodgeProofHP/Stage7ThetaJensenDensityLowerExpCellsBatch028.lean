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
theorem hpThetaDensityLowerExpCompact_cell560 :
    ∀ t ∈ Set.Icc ((42563 / 512000) : ℝ) (42571 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((29522053 / 25000000) : ℝ) ≤ Real.exp (2 * (42563 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42563 / 512000)) (29522053 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42571 / 512000) : ℝ)) ≤ (73807439 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42571 / 512000)) (73807439 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6813339431 / 100000) : ℝ) ≤ Real.exp (3 * (3709741 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3709741 / 1000000)) (6813339431 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42563 / 512000) : ℝ) (42571 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3709741 / 1000000) (463747 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42563 / 512000) (42571 / 512000) (29522053 / 25000000) (73807439 / 62500000) (3709741 / 1000000) (463747 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42563 / 512000) (42571 / 512000) (3709741 / 1000000) (463747 / 125000) (8197 / 250) (16399 / 500)
    (51161 / 1000) (10259 / 200) (-555) (385263 / 1000000) (3031129 / 1000) (469667 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3709741 / 1000000) (6813339431 / 100000) (469667 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3709741 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3709741 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell561 :
    ∀ t ∈ Set.Icc ((42571 / 512000) : ℝ) (42579 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1180919023 / 1000000000) : ℝ) ≤ Real.exp (2 * (42571 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42571 / 512000)) (1180919023 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42579 / 512000) : ℝ)) ≤ (147619491 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42579 / 512000)) (147619491 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((13631421769 / 200000) : ℝ) ≤ Real.exp (3 * (3709857 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3709857 / 1000000)) (13631421769 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42571 / 512000) : ℝ) (42579 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3709857 / 1000000) (927523 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42571 / 512000) (42579 / 512000) (1180919023 / 1000000000) (147619491 / 125000000) (3709857 / 1000000) (927523 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42571 / 512000) (42579 / 512000) (3709857 / 1000000) (927523 / 250000) (32791 / 1000) (164 / 5)
    (2047 / 40) (5131 / 100) (-27751 / 50) (77033 / 200000) (757877 / 250) (939007 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3709857 / 1000000) (13631421769 / 200000) (939007 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3709857 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3709857 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell562 :
    ∀ t ∈ Set.Icc ((42579 / 512000) : ℝ) (42587 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1180955927 / 1000000000) : ℝ) ≤ Real.exp (2 * (42579 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42579 / 512000)) (1180955927 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42587 / 512000) : ℝ)) ≤ (590496417 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42587 / 512000)) (590496417 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((13636166327 / 200000) : ℝ) ≤ Real.exp (3 * (3709973 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3709973 / 1000000)) (13636166327 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42579 / 512000) : ℝ) (42587 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3709973 / 1000000) (57972 / 15625) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42579 / 512000) (42587 / 512000) (1180955927 / 1000000000) (590496417 / 500000000) (3709973 / 1000000) (57972 / 15625) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42579 / 512000) (42587 / 512000) (3709973 / 1000000) (57972 / 15625) (16397 / 500) (32803 / 1000)
    (51189 / 1000) (12831 / 250) (-555039 / 1000) (385067 / 1000000) (378986 / 125) (3754721 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3709973 / 1000000) (13636166327 / 200000) (3754721 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3709973 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3709973 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell563 :
    ∀ t ∈ Set.Icc ((42587 / 512000) : ℝ) (8519 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1180992833 / 1000000000) : ℝ) ≤ Real.exp (2 * (42587 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42587 / 512000)) (1180992833 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8519 / 102400) : ℝ)) ≤ (59051487 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8519 / 102400)) (59051487 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((17051089517 / 250000) : ℝ) ≤ Real.exp (3 * (463761 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (463761 / 125000)) (17051089517 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42587 / 512000) : ℝ) (8519 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (463761 / 125000) (927581 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42587 / 512000) (8519 / 102400) (1180992833 / 1000000000) (59051487 / 50000000) (463761 / 125000) (927581 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42587 / 512000) (8519 / 102400) (463761 / 125000) (927581 / 250000) (32797 / 1000) (16403 / 500)
    (51203 / 1000) (25669 / 500) (-277527 / 500) (384971 / 1000000) (3032267 / 1000) (1876713 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (463761 / 125000) (17051089517 / 250000) (1876713 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (463761 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (463761 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell564 :
    ∀ t ∈ Set.Icc ((8519 / 102400) : ℝ) (42603 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1181029739 / 1000000000) : ℝ) ≤ Real.exp (2 * (8519 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8519 / 102400)) (1181029739 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42603 / 512000) : ℝ)) ≤ (147633331 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42603 / 512000)) (147633331 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8528512163 / 125000) : ℝ) ≤ Real.exp (3 * (927551 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (927551 / 250000)) (8528512163 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8519 / 102400) : ℝ) (42603 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (927551 / 250000) (3710439 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8519 / 102400) (42603 / 512000) (1181029739 / 1000000000) (147633331 / 125000000) (927551 / 250000) (3710439 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8519 / 102400) (42603 / 512000) (927551 / 250000) (3710439 / 1000000) (32799 / 1000) (32809 / 1000)
    (25609 / 500) (6419 / 125) (-277539 / 500) (48109 / 125000) (3032643 / 1000) (93803 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (927551 / 250000) (8528512163 / 125000) (93803 / 25000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (927551 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (927551 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell565 :
    ∀ t ∈ Set.Icc ((42603 / 512000) : ℝ) (42611 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1181066647 / 1000000000) : ℝ) ≤ Real.exp (2 * (42603 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42603 / 512000)) (1181066647 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42611 / 512000) : ℝ)) ≤ (1181103557 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42611 / 512000)) (1181103557 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((34125922401 / 500000) : ℝ) ≤ Real.exp (3 * (46379 / 12500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (46379 / 12500)) (34125922401 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42603 / 512000) : ℝ) (42611 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (46379 / 12500) (742111 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42603 / 512000) (42611 / 512000) (1181066647 / 1000000000) (1181103557 / 1000000000) (46379 / 12500) (742111 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42603 / 512000) (42611 / 512000) (46379 / 12500) (742111 / 200000) (16401 / 500) (32811 / 1000)
    (6404 / 125) (25683 / 500) (-277549 / 500) (15391 / 40000) (1516511 / 500) (750163 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (46379 / 12500) (34125922401 / 500000) (750163 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (46379 / 12500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (46379 / 12500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell566 :
    ∀ t ∈ Set.Icc ((42611 / 512000) : ℝ) (42619 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((295275889 / 250000000) : ℝ) ≤ Real.exp (2 * (42611 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42611 / 512000)) (295275889 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42619 / 512000) : ℝ)) ≤ (1181140467 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42619 / 512000)) (1181140467 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((13655120113 / 200000) : ℝ) ≤ Real.exp (3 * (927609 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (927609 / 250000)) (13655120113 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42611 / 512000) : ℝ) (42619 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (927609 / 250000) (3710671 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42611 / 512000) (42619 / 512000) (295275889 / 250000000) (1181140467 / 1000000000) (927609 / 250000) (3710671 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42611 / 512000) (42619 / 512000) (927609 / 250000) (3710671 / 1000000) (6561 / 200) (16407 / 500)
    (25623 / 500) (51381 / 1000) (-277559 / 500) (384677 / 1000000) (3033401 / 1000) (374951 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (927609 / 250000) (13655120113 / 200000) (374951 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (927609 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (927609 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell567 :
    ∀ t ∈ Set.Icc ((42619 / 512000) : ℝ) (42627 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((590570233 / 500000000) : ℝ) ≤ Real.exp (2 * (42619 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42619 / 512000)) (590570233 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42627 / 512000) : ℝ)) ≤ (590588689 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42627 / 512000)) (590588689 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((68299364597 / 1000000) : ℝ) ≤ Real.exp (3 * (463819 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (463819 / 125000)) (68299364597 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42619 / 512000) : ℝ) (42627 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (463819 / 125000) (3710787 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42619 / 512000) (42627 / 512000) (590570233 / 500000000) (590588689 / 500000000) (463819 / 125000) (3710787 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42619 / 512000) (42627 / 512000) (463819 / 125000) (3710787 / 1000000) (4101 / 125) (32817 / 1000)
    (2563 / 50) (10279 / 200) (-555137 / 1000) (384579 / 1000000) (3033781 / 1000) (749641 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (463819 / 125000) (68299364597 / 1000000) (749641 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (463819 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (463819 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell568 :
    ∀ t ∈ Set.Icc ((42627 / 512000) : ℝ) (8527 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1181177377 / 1000000000) : ℝ) ≤ Real.exp (2 * (42627 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42627 / 512000)) (1181177377 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8527 / 102400) : ℝ)) ≤ (1181214291 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8527 / 102400)) (1181214291 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((683231369 / 10000) : ℝ) ≤ Real.exp (3 * (927667 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (927667 / 250000)) (683231369 / 10000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42627 / 512000) : ℝ) (8527 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (927667 / 250000) (3710903 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42627 / 512000) (8527 / 102400) (1181177377 / 1000000000) (1181214291 / 1000000000) (927667 / 250000) (3710903 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42627 / 512000) (8527 / 102400) (927667 / 250000) (3710903 / 1000000) (3281 / 100) (1641 / 50)
    (2051 / 40) (51409 / 1000) (-555157 / 1000) (384481 / 1000000) (75854 / 25) (3746901 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (927667 / 250000) (683231369 / 10000) (3746901 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (927667 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (927667 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell569 :
    ∀ t ∈ Set.Icc ((8527 / 102400) : ℝ) (42643 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((118121429 / 100000000) : ℝ) ≤ Real.exp (2 * (8527 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8527 / 102400)) (118121429 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42643 / 512000) : ℝ)) ≤ (295312801 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42643 / 512000)) (295312801 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((34173458739 / 500000) : ℝ) ≤ Real.exp (3 * (57981 / 15625)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (57981 / 15625)) (34173458739 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8527 / 102400) : ℝ) (42643 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (57981 / 15625) (3711019 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8527 / 102400) (42643 / 512000) (118121429 / 100000000) (295312801 / 250000000) (57981 / 15625) (3711019 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8527 / 102400) (42643 / 512000) (57981 / 15625) (3711019 / 1000000) (32813 / 1000) (16411 / 500)
    (51289 / 1000) (51423 / 1000) (-69397 / 125) (6006 / 15625) (3034539 / 1000) (3745597 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (57981 / 15625) (34173458739 / 500000) (3745597 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (57981 / 15625)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (57981 / 15625)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell570 :
    ∀ t ∈ Set.Icc ((42643 / 512000) : ℝ) (42651 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1181251203 / 1000000000) : ℝ) ≤ Real.exp (2 * (42643 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42643 / 512000)) (1181251203 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42651 / 512000) : ℝ)) ≤ (1181288119 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42651 / 512000)) (1181288119 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((17092676583 / 250000) : ℝ) ≤ Real.exp (3 * (37109 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (37109 / 10000)) (17092676583 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42643 / 512000) : ℝ) (42651 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (37109 / 10000) (742227 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42643 / 512000) (42651 / 512000) (1181251203 / 1000000000) (1181288119 / 1000000000) (37109 / 10000) (742227 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42643 / 512000) (42651 / 512000) (37109 / 10000) (742227 / 200000) (4102 / 125) (1313 / 40)
    (51303 / 1000) (25719 / 500) (-138799 / 250) (192143 / 500000) (3034919 / 1000) (1872147 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (37109 / 10000) (17092676583 / 250000) (1872147 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (37109 / 10000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (37109 / 10000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell571 :
    ∀ t ∈ Set.Icc ((42651 / 512000) : ℝ) (42659 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((590644059 / 500000000) : ℝ) ≤ Real.exp (2 * (42651 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42651 / 512000)) (590644059 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42659 / 512000) : ℝ)) ≤ (236265007 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42659 / 512000)) (236265007 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((68394503467 / 1000000) : ℝ) ≤ Real.exp (3 * (463877 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (463877 / 125000)) (68394503467 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42651 / 512000) : ℝ) (42659 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (463877 / 125000) (3711251 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42651 / 512000) (42659 / 512000) (590644059 / 500000000) (236265007 / 200000000) (463877 / 125000) (3711251 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42651 / 512000) (42659 / 512000) (463877 / 125000) (3711251 / 1000000) (32819 / 1000) (8207 / 250)
    (51317 / 1000) (12863 / 250) (-111043 / 200) (96047 / 250000) (1517649 / 500) (3742991 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (463877 / 125000) (68394503467 / 1000000) (3742991 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (463877 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (463877 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell572 :
    ∀ t ∈ Set.Icc ((42659 / 512000) : ℝ) (42667 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((590662517 / 500000000) : ℝ) ≤ Real.exp (2 * (42659 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42659 / 512000)) (590662517 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42667 / 512000) : ℝ)) ≤ (36917561 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42667 / 512000)) (36917561 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((17104577221 / 250000) : ℝ) ≤ Real.exp (3 * (927783 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (927783 / 250000)) (17104577221 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42659 / 512000) : ℝ) (42667 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (927783 / 250000) (3711367 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42659 / 512000) (42667 / 512000) (590662517 / 500000000) (36917561 / 31250000) (927783 / 250000) (3711367 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42659 / 512000) (42667 / 512000) (927783 / 250000) (3711367 / 1000000) (32821 / 1000) (32831 / 1000)
    (12833 / 250) (25733 / 500) (-111047 / 200) (384091 / 1000000) (1517839 / 500) (3741689 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (927783 / 250000) (17104577221 / 250000) (3741689 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (927783 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (927783 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell573 :
    ∀ t ∈ Set.Icc ((42667 / 512000) : ℝ) (1707 / 20480), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1181361951 / 1000000000) : ℝ) ≤ Real.exp (2 * (42667 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42667 / 512000)) (1181361951 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1707 / 20480) : ℝ)) ≤ (118139887 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1707 / 20480)) (118139887 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((68442122587 / 1000000) : ℝ) ≤ Real.exp (3 * (231953 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (231953 / 62500)) (68442122587 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42667 / 512000) : ℝ) (1707 / 20480),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (231953 / 62500) (3711483 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42667 / 512000) (1707 / 20480) (1181361951 / 1000000000) (118139887 / 100000000) (231953 / 62500) (3711483 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42667 / 512000) (1707 / 20480) (231953 / 62500) (3711483 / 1000000) (4103 / 125) (32833 / 1000)
    (25673 / 500) (1287 / 25) (-277627 / 500) (383993 / 1000000) (3036057 / 1000) (3740387 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (231953 / 62500) (68442122587 / 1000000) (3740387 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (231953 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (231953 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell574 :
    ∀ t ∈ Set.Icc ((1707 / 20480) : ℝ) (42683 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1181398869 / 1000000000) : ℝ) ≤ Real.exp (2 * (1707 / 20480)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1707 / 20480)) (1181398869 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42683 / 512000) : ℝ)) ≤ (1181435789 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42683 / 512000)) (1181435789 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((68465944579 / 1000000) : ℝ) ≤ Real.exp (3 * (927841 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (927841 / 250000)) (68465944579 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1707 / 20480) : ℝ) (42683 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (927841 / 250000) (3711599 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1707 / 20480) (42683 / 512000) (1181398869 / 1000000000) (1181435789 / 1000000000) (927841 / 250000) (3711599 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1707 / 20480) (42683 / 512000) (927841 / 250000) (3711599 / 1000000) (32827 / 1000) (8209 / 250)
    (1284 / 25) (10299 / 200) (-277637 / 500) (76779 / 200000) (3036437 / 1000) (1869543 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (927841 / 250000) (68465944579 / 1000000) (1869543 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (927841 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (927841 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell575 :
    ∀ t ∈ Set.Icc ((42683 / 512000) : ℝ) (42691 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((295358947 / 250000000) : ℝ) ≤ Real.exp (2 * (42683 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42683 / 512000)) (295358947 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42691 / 512000) : ℝ)) ≤ (1181472709 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42691 / 512000)) (1181472709 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((34244887431 / 500000) : ℝ) ≤ Real.exp (3 * (92787 / 25000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (92787 / 25000)) (34244887431 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42683 / 512000) : ℝ) (42691 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (92787 / 25000) (742343 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42683 / 512000) (42691 / 512000) (295358947 / 250000000) (1181472709 / 1000000000) (92787 / 25000) (742343 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42683 / 512000) (42691 / 512000) (92787 / 25000) (742343 / 200000) (3283 / 100) (32839 / 1000)
    (25687 / 500) (51509 / 1000) (-277647 / 500) (191899 / 500000) (379602 / 125) (747557 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (92787 / 25000) (34244887431 / 500000) (747557 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (92787 / 25000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (92787 / 25000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell576 :
    ∀ t ∈ Set.Icc ((42691 / 512000) : ℝ) (42699 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((295368177 / 250000000) : ℝ) ≤ Real.exp (2 * (42691 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42691 / 512000)) (295368177 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42699 / 512000) : ℝ)) ≤ (1181509631 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42699 / 512000)) (1181509631 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((68513613439 / 1000000) : ℝ) ≤ Real.exp (3 * (927899 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (927899 / 250000)) (68513613439 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42691 / 512000) : ℝ) (42699 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (927899 / 250000) (3711831 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42691 / 512000) (42699 / 512000) (295368177 / 250000000) (1181509631 / 1000000000) (927899 / 250000) (3711831 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42691 / 512000) (42699 / 512000) (927899 / 250000) (3711831 / 1000000) (4104 / 125) (16421 / 500)
    (51389 / 1000) (51523 / 1000) (-555313 / 1000) (3837 / 10000) (759299 / 250) (934121 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (927899 / 250000) (68513613439 / 1000000) (934121 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (927899 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (927899 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell577 :
    ∀ t ∈ Set.Icc ((42699 / 512000) : ℝ) (42707 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((118150963 / 100000000) : ℝ) ≤ Real.exp (2 * (42699 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42699 / 512000)) (118150963 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42707 / 512000) : ℝ)) ≤ (590773277 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42707 / 512000)) (590773277 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((34268730157 / 500000) : ℝ) ≤ Real.exp (3 * (115991 / 31250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (115991 / 31250)) (34268730157 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42699 / 512000) : ℝ) (42707 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (115991 / 31250) (3711947 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42699 / 512000) (42707 / 512000) (118150963 / 100000000) (590773277 / 500000000) (115991 / 31250) (3711947 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42699 / 512000) (42707 / 512000) (115991 / 31250) (3711947 / 1000000) (6567 / 200) (8211 / 250)
    (51403 / 1000) (25769 / 500) (-555333 / 1000) (383603 / 1000000) (379697 / 125) (233449 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (115991 / 31250) (34268730157 / 500000) (233449 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (115991 / 31250)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (115991 / 31250)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell578 :
    ∀ t ∈ Set.Icc ((42707 / 512000) : ℝ) (8543 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1181546553 / 1000000000) : ℝ) ≤ Real.exp (2 * (42707 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (42707 / 512000)) (1181546553 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8543 / 102400) : ℝ)) ≤ (590791739 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8543 / 102400)) (590791739 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((68561315489 / 1000000) : ℝ) ≤ Real.exp (3 * (927957 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (927957 / 250000)) (68561315489 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((42707 / 512000) : ℝ) (8543 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (927957 / 250000) (3712063 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (42707 / 512000) (8543 / 102400) (1181546553 / 1000000000) (590791739 / 500000000) (927957 / 250000) (3712063 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (42707 / 512000) (8543 / 102400) (927957 / 250000) (3712063 / 1000000) (16419 / 500) (32847 / 1000)
    (51417 / 1000) (6444 / 125) (-69419 / 125) (76701 / 200000) (607591 / 200) (746777 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (927957 / 250000) (68561315489 / 1000000) (746777 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (927957 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (927957 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell579 :
    ∀ t ∈ Set.Icc ((8543 / 102400) : ℝ) (42723 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1181583477 / 1000000000) : ℝ) ≤ Real.exp (2 * (8543 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8543 / 102400)) (1181583477 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((42723 / 512000) : ℝ)) ≤ (1181620403 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (42723 / 512000)) (1181620403 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((68585178967 / 1000000) : ℝ) ≤ Real.exp (3 * (463993 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (463993 / 125000)) (68585178967 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8543 / 102400) : ℝ) (42723 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (463993 / 125000) (3712179 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8543 / 102400) (42723 / 512000) (1181583477 / 1000000000) (1181620403 / 1000000000) (463993 / 125000) (3712179 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8543 / 102400) (42723 / 512000) (463993 / 125000) (3712179 / 1000000) (32841 / 1000) (657 / 20)
    (51431 / 1000) (25783 / 500) (-138843 / 250) (23963 / 62500) (607667 / 200) (746517 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (463993 / 125000) (68585178967 / 1000000) (746517 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (463993 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (463993 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch028 :
    ∀ t ∈ Set.Icc ((42563 / 512000) : ℝ) (42723 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell560
      hpThetaDensityLowerExpCompact_cell561)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell562
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell563
      hpThetaDensityLowerExpCompact_cell564)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell565
      hpThetaDensityLowerExpCompact_cell566)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell567
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell568
      hpThetaDensityLowerExpCompact_cell569))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell570
      hpThetaDensityLowerExpCompact_cell571)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell572
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell573
      hpThetaDensityLowerExpCompact_cell574)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell575
      hpThetaDensityLowerExpCompact_cell576)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell577
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell578
      hpThetaDensityLowerExpCompact_cell579)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch028
end HodgeProofHP
