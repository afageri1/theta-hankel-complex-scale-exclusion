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
theorem hpThetaDensityLowerExpCompact_cell140 :
    ∀ t ∈ Set.Icc ((411 / 5120) : ℝ) (41101 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((117415281 / 100000000) : ℝ) ≤ Real.exp (2 * (411 / 5120)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (411 / 5120)) (117415281 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41101 / 512000) : ℝ)) ≤ (1174157397 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41101 / 512000)) (1174157397 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((511572357 / 8000) : ℝ) ≤ Real.exp (3 * (3688601 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3688601 / 1000000)) (511572357 / 8000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((411 / 5120) : ℝ) (41101 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3688601 / 1000000) (3688733 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (411 / 5120) (41101 / 512000) (117415281 / 100000000) (1174157397 / 1000000000) (3688601 / 1000000) (3688733 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (411 / 5120) (41101 / 512000) (3688601 / 1000000) (3688733 / 1000000) (3229 / 100) (4037 / 125)
    (6077 / 125) (12173 / 250) (-551773 / 1000) (403477 / 1000000) (2962299 / 1000) (250209 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3688601 / 1000000) (511572357 / 8000) (250209 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688601 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688601 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell141 :
    ∀ t ∈ Set.Icc ((41101 / 512000) : ℝ) (20551 / 256000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((293539349 / 250000000) : ℝ) ≤ Real.exp (2 * (41101 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41101 / 512000)) (293539349 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((20551 / 256000) : ℝ)) ≤ (18346281 / 15625000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (20551 / 256000)) (18346281 / 15625000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((12789846087 / 200000) : ℝ) ≤ Real.exp (3 * (737723 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (737723 / 200000)) (12789846087 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41101 / 512000) : ℝ) (20551 / 256000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (737723 / 200000) (922187 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41101 / 512000) (20551 / 256000) (293539349 / 250000000) (18346281 / 15625000) (737723 / 200000) (922187 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41101 / 512000) (20551 / 256000) (737723 / 200000) (922187 / 250000) (32291 / 1000) (4037 / 125)
    (24309 / 500) (24347 / 500) (-551771 / 1000) (80693 / 200000) (740587 / 250) (500397 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (737723 / 200000) (12789846087 / 200000) (500397 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (737723 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (737723 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell142 :
    ∀ t ∈ Set.Icc ((20551 / 256000) : ℝ) (41103 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174161983 / 1000000000) : ℝ) ≤ Real.exp (2 * (20551 / 256000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (20551 / 256000)) (1174161983 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41103 / 512000) : ℝ)) ≤ (117416657 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41103 / 512000)) (117416657 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31975958179 / 500000) : ℝ) ≤ Real.exp (3 * (3688629 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3688629 / 1000000)) (31975958179 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((20551 / 256000) : ℝ) (41103 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3688629 / 1000000) (1844381 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (20551 / 256000) (41103 / 512000) (1174161983 / 1000000000) (117416657 / 100000000) (3688629 / 1000000) (1844381 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (20551 / 256000) (41103 / 512000) (3688629 / 1000000) (1844381 / 500000) (32291 / 1000) (32297 / 1000)
    (48619 / 1000) (9739 / 200) (-275887 / 500) (403453 / 1000000) (370299 / 125) (62547 / 15625000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3688629 / 1000000) (31975958179 / 500000) (62547 / 15625000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688629 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688629 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell143 :
    ∀ t ∈ Set.Icc ((41103 / 512000) : ℝ) (2569 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174166569 / 1000000000) : ℝ) ≤ Real.exp (2 * (41103 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41103 / 512000)) (1174166569 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2569 / 32000) : ℝ)) ≤ (1174171157 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2569 / 32000)) (1174171157 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31977397129 / 500000) : ℝ) ≤ Real.exp (3 * (922161 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (922161 / 250000)) (31977397129 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41103 / 512000) : ℝ) (2569 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (922161 / 250000) (3688777 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41103 / 512000) (2569 / 32000) (1174166569 / 1000000000) (1174171157 / 1000000000) (922161 / 250000) (3688777 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41103 / 512000) (2569 / 32000) (922161 / 250000) (3688777 / 1000000) (32291 / 1000) (32297 / 1000)
    (48621 / 1000) (48697 / 1000) (-68972 / 125) (403439 / 1000000) (2962441 / 1000) (1000707 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (922161 / 250000) (31977397129 / 500000) (1000707 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922161 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922161 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell144 :
    ∀ t ∈ Set.Icc ((2569 / 32000) : ℝ) (8221 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((293542789 / 250000000) : ℝ) ≤ Real.exp (2 * (2569 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2569 / 32000)) (293542789 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8221 / 102400) : ℝ)) ≤ (2293312 / 1953125) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8221 / 102400)) (2293312 / 1953125) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31978740207 / 500000) : ℝ) ≤ Real.exp (3 * (1844329 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1844329 / 500000)) (31978740207 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2569 / 32000) : ℝ) (8221 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1844329 / 500000) (3688791 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2569 / 32000) (8221 / 102400) (293542789 / 250000000) (2293312 / 1953125) (1844329 / 500000) (3688791 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2569 / 32000) (8221 / 102400) (1844329 / 500000) (3688791 / 1000000) (8073 / 250) (32297 / 1000)
    (48623 / 1000) (48699 / 1000) (-551779 / 1000) (403427 / 1000000) (1481243 / 500) (200133 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1844329 / 500000) (31978740207 / 500000) (200133 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844329 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844329 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell145 :
    ∀ t ∈ Set.Icc ((8221 / 102400) : ℝ) (41107 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174175743 / 1000000000) : ℝ) ≤ Real.exp (2 * (8221 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8221 / 102400)) (1174175743 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41107 / 512000) : ℝ)) ≤ (1174184917 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41107 / 512000)) (1174184917 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((15990089641 / 250000) : ℝ) ≤ Real.exp (3 * (3688673 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3688673 / 1000000)) (15990089641 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8221 / 102400) : ℝ) (41107 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3688673 / 1000000) (184441 / 50000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8221 / 102400) (41107 / 512000) (1174175743 / 1000000000) (1174184917 / 1000000000) (3688673 / 1000000) (184441 / 50000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8221 / 102400) (41107 / 512000) (3688673 / 1000000) (184441 / 50000) (8073 / 250) (16149 / 500)
    (24311 / 500) (9741 / 200) (-13793 / 25) (201709 / 500000) (2962579 / 1000) (50031 / 12500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3688673 / 1000000) (15990089641 / 250000) (50031 / 12500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688673 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688673 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell146 :
    ∀ t ∈ Set.Icc ((41107 / 512000) : ℝ) (10277 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((293546229 / 250000000) : ℝ) ≤ Real.exp (2 * (41107 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41107 / 512000)) (293546229 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((10277 / 128000) : ℝ)) ≤ (18346711 / 15625000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (10277 / 128000)) (18346711 / 15625000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31982865729 / 500000) : ℝ) ≤ Real.exp (3 * (3688701 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3688701 / 1000000)) (31982865729 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41107 / 512000) : ℝ) (10277 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3688701 / 1000000) (1844417 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41107 / 512000) (10277 / 128000) (293546229 / 250000000) (18346711 / 15625000) (3688701 / 1000000) (1844417 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41107 / 512000) (10277 / 128000) (3688701 / 1000000) (1844417 / 500000) (32293 / 1000) (16149 / 500)
    (12157 / 250) (6088 / 125) (-551787 / 1000) (403389 / 1000000) (370328 / 125) (4002143 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3688701 / 1000000) (31982865729 / 500000) (4002143 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688701 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688701 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell147 :
    ∀ t ∈ Set.Icc ((10277 / 128000) : ℝ) (41109 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174189503 / 1000000000) : ℝ) ≤ Real.exp (2 * (10277 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (10277 / 128000)) (1174189503 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41109 / 512000) : ℝ)) ≤ (117419409 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41109 / 512000)) (117419409 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63968609979 / 1000000) : ℝ) ≤ Real.exp (3 * (922179 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (922179 / 250000)) (63968609979 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((10277 / 128000) : ℝ) (41109 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (922179 / 250000) (3688849 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (10277 / 128000) (41109 / 512000) (1174189503 / 1000000000) (117419409 / 100000000) (922179 / 250000) (3688849 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (10277 / 128000) (41109 / 512000) (922179 / 250000) (3688849 / 1000000) (32293 / 1000) (32299 / 1000)
    (4863 / 100) (24353 / 500) (-551789 / 1000) (25211 / 62500) (370334 / 125) (4001963 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (922179 / 250000) (63968609979 / 1000000) (4001963 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922179 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922179 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell148 :
    ∀ t ∈ Set.Icc ((41109 / 512000) : ℝ) (41111 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174194089 / 1000000000) : ℝ) ≤ Real.exp (2 * (41109 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41109 / 512000)) (1174194089 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41111 / 512000) : ℝ)) ≤ (9173463 / 7812500) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41111 / 512000)) (9173463 / 7812500) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((15992824179 / 250000) : ℝ) ≤ Real.exp (3 * (368873 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (368873 / 100000)) (15992824179 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41109 / 512000) : ℝ) (41111 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (368873 / 100000) (3688877 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41109 / 512000) (41111 / 512000) (1174194089 / 1000000000) (9173463 / 7812500) (368873 / 100000) (3688877 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41109 / 512000) (41111 / 512000) (368873 / 100000) (3688877 / 1000000) (32293 / 1000) (32299 / 1000)
    (12157 / 250) (6089 / 125) (-55173 / 100) (50421 / 125000) (1481381 / 500) (800359 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (368873 / 100000) (15992824179 / 250000) (800359 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (368873 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (368873 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell149 :
    ∀ t ∈ Set.Icc ((41111 / 512000) : ℝ) (5139 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174203263 / 1000000000) : ℝ) ≤ Real.exp (2 * (41111 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41111 / 512000)) (1174203263 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((5139 / 64000) : ℝ)) ≤ (23484157 / 20000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (5139 / 64000)) (23484157 / 20000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31988431229 / 500000) : ℝ) ≤ Real.exp (3 * (3688759 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3688759 / 1000000)) (31988431229 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41111 / 512000) : ℝ) (5139 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3688759 / 1000000) (922223 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41111 / 512000) (5139 / 64000) (1174203263 / 1000000000) (23484157 / 20000000) (3688759 / 1000000) (922223 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41111 / 512000) (5139 / 64000) (3688759 / 1000000) (922223 / 250000) (16147 / 500) (323 / 10)
    (9727 / 200) (48711 / 1000) (-551797 / 1000) (201669 / 500000) (296281 / 100) (4001447 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3688759 / 1000000) (31988431229 / 500000) (4001447 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688759 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688759 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell150 :
    ∀ t ∈ Set.Icc ((5139 / 64000) : ℝ) (41113 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174207849 / 1000000000) : ℝ) ≤ Real.exp (2 * (5139 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (5139 / 64000)) (1174207849 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41113 / 512000) : ℝ)) ≤ (1174212437 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41113 / 512000)) (1174212437 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31989774771 / 500000) : ℝ) ≤ Real.exp (3 * (3688773 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3688773 / 1000000)) (31989774771 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((5139 / 64000) : ℝ) (41113 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3688773 / 1000000) (1844453 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (5139 / 64000) (41113 / 512000) (1174207849 / 1000000000) (1174212437 / 1000000000) (3688773 / 1000000) (1844453 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (5139 / 64000) (41113 / 512000) (3688773 / 1000000) (1844453 / 500000) (16147 / 500) (323 / 10)
    (48637 / 1000) (48713 / 1000) (-2759 / 5) (201663 / 500000) (592571 / 200) (4001279 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3688773 / 1000000) (31989774771 / 500000) (4001279 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688773 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688773 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell151 :
    ∀ t ∈ Set.Icc ((41113 / 512000) : ℝ) (8223 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((293553109 / 250000000) : ℝ) ≤ Real.exp (2 * (41113 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41113 / 512000)) (293553109 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((8223 / 102400) : ℝ)) ≤ (1174221611 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8223 / 102400)) (1174221611 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((12796485737 / 200000) : ℝ) ≤ Real.exp (3 * (922197 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (922197 / 250000)) (12796485737 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41113 / 512000) : ℝ) (8223 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (922197 / 250000) (737787 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41113 / 512000) (8223 / 102400) (293553109 / 250000000) (1174221611 / 1000000000) (922197 / 250000) (737787 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41113 / 512000) (8223 / 102400) (922197 / 250000) (737787 / 200000) (6459 / 200) (32301 / 1000)
    (9727 / 200) (48719 / 1000) (-27587 / 50) (403317 / 1000000) (740737 / 250) (4001099 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (922197 / 250000) (12796485737 / 200000) (4001099 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922197 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (922197 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell152 :
    ∀ t ∈ Set.Icc ((8223 / 102400) : ℝ) (41117 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((117422161 / 100000000) : ℝ) ≤ Real.exp (2 * (8223 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8223 / 102400)) (117422161 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41117 / 512000) : ℝ)) ≤ (4586839 / 3906250) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41117 / 512000)) (4586839 / 3906250) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((15996998849 / 250000) : ℝ) ≤ Real.exp (3 * (3688817 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3688817 / 1000000)) (15996998849 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((8223 / 102400) : ℝ) (41117 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3688817 / 1000000) (922241 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (8223 / 102400) (41117 / 512000) (117422161 / 100000000) (4586839 / 3906250) (3688817 / 1000000) (922241 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (8223 / 102400) (41117 / 512000) (3688817 / 1000000) (922241 / 250000) (6459 / 200) (32301 / 1000)
    (48639 / 1000) (48723 / 1000) (-110349 / 200) (403291 / 1000000) (2963041 / 1000) (4000751 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3688817 / 1000000) (15996998849 / 250000) (4000751 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688817 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688817 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell153 :
    ∀ t ∈ Set.Icc ((41117 / 512000) : ℝ) (41119 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174230783 / 1000000000) : ℝ) ≤ Real.exp (2 * (41117 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41117 / 512000)) (1174230783 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41119 / 512000) : ℝ)) ≤ (587119979 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41119 / 512000)) (587119979 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63993562591 / 1000000) : ℝ) ≤ Real.exp (3 * (1844423 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1844423 / 500000)) (63993562591 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41117 / 512000) : ℝ) (41119 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1844423 / 500000) (3688993 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41117 / 512000) (41119 / 512000) (1174230783 / 1000000000) (587119979 / 500000000) (1844423 / 500000) (3688993 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41117 / 512000) (41119 / 512000) (1844423 / 500000) (3688993 / 1000000) (4037 / 125) (16151 / 500)
    (24321 / 500) (24363 / 500) (-551751 / 1000) (201633 / 500000) (592627 / 200) (4000403 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1844423 / 500000) (63993562591 / 1000000) (4000403 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844423 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844423 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell154 :
    ∀ t ∈ Set.Icc ((41119 / 512000) : ℝ) (257 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174239957 / 1000000000) : ℝ) ≤ Real.exp (2 * (41119 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41119 / 512000)) (1174239957 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((257 / 3200) : ℝ)) ≤ (234848909 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (257 / 3200)) (234848909 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31999469137 / 500000) : ℝ) ≤ Real.exp (3 * (1844437 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1844437 / 500000)) (31999469137 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41119 / 512000) : ℝ) (257 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1844437 / 500000) (3689007 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41119 / 512000) (257 / 3200) (1174239957 / 1000000000) (234848909 / 200000000) (1844437 / 500000) (3689007 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41119 / 512000) (257 / 3200) (1844437 / 500000) (3689007 / 1000000) (32297 / 1000) (16151 / 500)
    (48649 / 1000) (1949 / 40) (-275909 / 500) (403237 / 1000000) (148159 / 50) (4000067 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1844437 / 500000) (31999469137 / 500000) (4000067 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844437 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844437 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell155 :
    ∀ t ∈ Set.Icc ((257 / 3200) : ℝ) (20561 / 256000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((18347571 / 15625000) : ℝ) ≤ Real.exp (2 * (257 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (257 / 3200)) (18347571 / 15625000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((20561 / 256000) : ℝ)) ≤ (1174253719 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (20561 / 256000)) (1174253719 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6400181829 / 100000) : ℝ) ≤ Real.exp (3 * (3688889 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3688889 / 1000000)) (6400181829 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((257 / 3200) : ℝ) (20561 / 256000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3688889 / 1000000) (922259 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (257 / 3200) (20561 / 256000) (18347571 / 15625000) (1174253719 / 1000000000) (3688889 / 1000000) (922259 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (257 / 3200) (20561 / 256000) (3688889 / 1000000) (922259 / 250000) (32297 / 1000) (32303 / 1000)
    (6081 / 125) (48731 / 1000) (-275879 / 500) (100807 / 250000) (2963273 / 1000) (3999887 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3688889 / 1000000) (6400181829 / 100000) (3999887 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688889 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688889 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell156 :
    ∀ t ∈ Set.Icc ((20561 / 256000) : ℝ) (10281 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((587126859 / 500000000) : ℝ) ≤ Real.exp (2 * (20561 / 256000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (20561 / 256000)) (587126859 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((10281 / 128000) : ℝ)) ≤ (1174262893 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (10281 / 128000)) (1174262893 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1000115417 / 15625) : ℝ) ≤ Real.exp (3 * (1844459 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1844459 / 500000)) (1000115417 / 15625) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((20561 / 256000) : ℝ) (10281 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1844459 / 500000) (737813 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (20561 / 256000) (10281 / 128000) (587126859 / 500000000) (1174262893 / 1000000000) (1844459 / 500000) (737813 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (20561 / 256000) (10281 / 128000) (1844459 / 500000) (737813 / 200000) (16149 / 500) (4038 / 125)
    (48651 / 1000) (9747 / 200) (-551763 / 1000) (201601 / 500000) (1481683 / 500) (3999539 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1844459 / 500000) (1000115417 / 15625) (3999539 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844459 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844459 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell157 :
    ∀ t ∈ Set.Icc ((10281 / 128000) : ℝ) (329 / 4096), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((293565723 / 250000000) : ℝ) ≤ Real.exp (2 * (10281 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (10281 / 128000)) (293565723 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((329 / 4096) : ℝ)) ≤ (29356687 / 25000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (329 / 4096)) (29356687 / 25000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16003190883 / 250000) : ℝ) ≤ Real.exp (3 * (1844473 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1844473 / 500000)) (16003190883 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((10281 / 128000) : ℝ) (329 / 4096),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1844473 / 500000) (3689079 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (10281 / 128000) (329 / 4096) (293565723 / 250000000) (29356687 / 25000000) (1844473 / 500000) (3689079 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (10281 / 128000) (329 / 4096) (1844473 / 500000) (3689079 / 1000000) (16149 / 500) (4038 / 125)
    (24329 / 500) (48733 / 1000) (-551831 / 1000) (403173 / 1000000) (2963411 / 1000) (3999203 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1844473 / 500000) (16003190883 / 250000) (3999203 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844473 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1844473 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell158 :
    ∀ t ∈ Set.Icc ((329 / 4096) : ℝ) (41127 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174267479 / 1000000000) : ℝ) ≤ Real.exp (2 * (329 / 4096)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (329 / 4096)) (1174267479 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41127 / 512000) : ℝ)) ≤ (587138327 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41127 / 512000)) (587138327 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6401564417 / 100000) : ℝ) ≤ Real.exp (3 * (3688961 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3688961 / 1000000)) (6401564417 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((329 / 4096) : ℝ) (41127 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3688961 / 1000000) (922277 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (329 / 4096) (41127 / 512000) (1174267479 / 1000000000) (587138327 / 500000000) (3688961 / 1000000) (922277 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (329 / 4096) (41127 / 512000) (3688961 / 1000000) (922277 / 250000) (32299 / 1000) (6461 / 200)
    (6082 / 125) (2437 / 50) (-551771 / 1000) (100791 / 250000) (370438 / 125) (3999023 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3688961 / 1000000) (6401564417 / 100000) (3999023 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688961 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3688961 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell159 :
    ∀ t ∈ Set.Icc ((41127 / 512000) : ℝ) (41129 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1174276653 / 1000000000) : ℝ) ≤ Real.exp (2 * (41127 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41127 / 512000)) (1174276653 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41129 / 512000) : ℝ)) ≤ (293571457 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41129 / 512000)) (293571457 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((64021213771 / 1000000) : ℝ) ≤ Real.exp (3 * (368899 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (368899 / 100000)) (64021213771 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41127 / 512000) : ℝ) (41129 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (368899 / 100000) (3689137 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (41127 / 512000) (41129 / 512000) (1174276653 / 1000000000) (293571457 / 250000000) (368899 / 100000) (3689137 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (41127 / 512000) (41129 / 512000) (368899 / 100000) (3689137 / 1000000) (32299 / 1000) (6461 / 200)
    (2433 / 50) (48743 / 1000) (-68972 / 125) (403139 / 1000000) (2963597 / 1000) (159947 / 40000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (368899 / 100000) (64021213771 / 1000000) (159947 / 40000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (368899 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (368899 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch007 :
    ∀ t ∈ Set.Icc ((411 / 5120) : ℝ) (41129 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell140
      hpThetaDensityLowerExpCompact_cell141)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell142
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell143
      hpThetaDensityLowerExpCompact_cell144)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell145
      hpThetaDensityLowerExpCompact_cell146)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell147
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell148
      hpThetaDensityLowerExpCompact_cell149))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell150
      hpThetaDensityLowerExpCompact_cell151)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell152
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell153
      hpThetaDensityLowerExpCompact_cell154)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell155
      hpThetaDensityLowerExpCompact_cell156)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell157
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell158
      hpThetaDensityLowerExpCompact_cell159)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch007
end HodgeProofHP
