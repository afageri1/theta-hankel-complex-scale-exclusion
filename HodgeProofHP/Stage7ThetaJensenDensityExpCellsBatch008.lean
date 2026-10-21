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
theorem hpThetaDensityExpCompact_cell160 :
    ∀ t ∈ Set.Icc ((1901 / 16000) : ℝ) (1903 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((317058379 / 250000000) : ℝ) ≤ Real.exp (2 * (1901 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1901 / 16000)) (317058379 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1903 / 16000) : ℝ)) ≤ (253710123 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1903 / 16000)) (253710123 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((77599531881 / 500000) : ℝ) ≤ Real.exp (3 * (796831 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (796831 / 200000)) (77599531881 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1901 / 16000) : ℝ) (1903 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (796831 / 200000) (3985279 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1901 / 16000) (1903 / 16000) (317058379 / 250000000) (253710123 / 200000000) (796831 / 200000) (3985279 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1901 / 16000) (1903 / 16000) (796831 / 200000) (3985279 / 1000000) (19791 / 500) (317 / 8)
    (22307 / 250) (89943 / 1000) (-575921 / 1000) (209649 / 1000000) (807207 / 200) (329899 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (796831 / 200000) (77599531881 / 500000) (329899 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (796831 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (796831 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell161 :
    ∀ t ∈ Set.Icc ((1903 / 16000) : ℝ) (381 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((634275307 / 500000000) : ℝ) ≤ Real.exp (2 * (1903 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1903 / 16000)) (634275307 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((381 / 3200) : ℝ)) ≤ (79304237 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (381 / 3200)) (79304237 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31132698231 / 200000) : ℝ) ≤ Real.exp (3 * (3985151 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3985151 / 1000000)) (31132698231 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1903 / 16000) : ℝ) (381 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3985151 / 1000000) (996569 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1903 / 16000) (381 / 3200) (634275307 / 500000000) (79304237 / 62500000) (3985151 / 1000000) (996569 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1903 / 16000) (381 / 3200) (3985151 / 1000000) (996569 / 250000) (4951 / 125) (39651 / 1000)
    (11173 / 125) (901 / 10) (-14398 / 25) (10459 / 50000) (1010019 / 250) (822287 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3985151 / 1000000) (31132698231 / 200000) (822287 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3985151 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3985151 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell162 :
    ∀ t ∈ Set.Icc ((381 / 3200) : ℝ) (1907 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1268867791 / 1000000000) : ℝ) ≤ Real.exp (2 * (381 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (381 / 3200)) (1268867791 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1907 / 16000) : ℝ)) ≤ (158648131 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1907 / 16000)) (158648131 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((19516222089 / 125000) : ℝ) ≤ Real.exp (3 * (996537 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (996537 / 250000)) (19516222089 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((381 / 3200) : ℝ) (1907 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (996537 / 250000) (498409 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (381 / 3200) (1907 / 16000) (1268867791 / 1000000000) (158648131 / 125000000) (996537 / 250000) (498409 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (381 / 3200) (1907 / 16000) (996537 / 250000) (498409 / 125000) (39633 / 1000) (39677 / 1000)
    (89541 / 1000) (11282 / 125) (-575929 / 1000) (26089 / 125000) (808823 / 200) (819831 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (996537 / 250000) (19516222089 / 125000) (819831 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (996537 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (996537 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell163 :
    ∀ t ∈ Set.Icc ((1907 / 16000) : ℝ) (1909 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1269185047 / 1000000000) : ℝ) ≤ Real.exp (2 * (1907 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1907 / 16000)) (1269185047 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1909 / 16000) : ℝ)) ≤ (79343899 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1909 / 16000)) (79343899 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((7829849461 / 50000) : ℝ) ≤ Real.exp (3 * (498393 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (498393 / 125000)) (7829849461 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1907 / 16000) : ℝ) (1909 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (498393 / 125000) (3988269 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1907 / 16000) (1909 / 16000) (1269185047 / 1000000000) (79343899 / 62500000) (498393 / 125000) (3988269 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1907 / 16000) (1909 / 16000) (498393 / 125000) (3988269 / 1000000) (39659 / 1000) (39703 / 1000)
    (89697 / 1000) (45207 / 500) (-575927 / 1000) (41649 / 200000) (4048161 / 1000) (163477 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (498393 / 125000) (7829849461 / 50000) (163477 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (498393 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (498393 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell164 :
    ∀ t ∈ Set.Icc ((1909 / 16000) : ℝ) (1911 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1269502383 / 1000000000) : ℝ) ≤ Real.exp (2 * (1909 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1909 / 16000)) (1269502383 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1911 / 16000) : ℝ)) ≤ (6349099 / 5000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1911 / 16000)) (6349099 / 5000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31413214207 / 200000) : ℝ) ≤ Real.exp (3 * (3988141 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3988141 / 1000000)) (31413214207 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1909 / 16000) : ℝ) (1911 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3988141 / 1000000) (1994633 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1909 / 16000) (1911 / 16000) (1269502383 / 1000000000) (6349099 / 5000000) (3988141 / 1000000) (1994633 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1909 / 16000) (1911 / 16000) (3988141 / 1000000) (1994633 / 500000) (7937 / 200) (39729 / 1000)
    (44927 / 500) (90571 / 1000) (-575929 / 1000) (207779 / 1000000) (4052211 / 1000) (25467 / 15625000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3988141 / 1000000) (31413214207 / 200000) (25467 / 15625000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3988141 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3988141 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell165 :
    ∀ t ∈ Set.Icc ((1911 / 16000) : ℝ) (1913 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1269819799 / 1000000000) : ℝ) ≤ Real.exp (2 * (1911 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1911 / 16000)) (1269819799 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1913 / 16000) : ℝ)) ≤ (635068647 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1913 / 16000)) (635068647 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((157536557967 / 1000000) : ℝ) ≤ Real.exp (3 * (1994569 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1994569 / 500000)) (157536557967 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1911 / 16000) : ℝ) (1913 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1994569 / 500000) (498783 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1911 / 16000) (1913 / 16000) (1269819799 / 1000000000) (635068647 / 500000000) (1994569 / 500000) (498783 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1911 / 16000) (1913 / 16000) (1994569 / 500000) (498783 / 125000) (39711 / 1000) (19877 / 500)
    (90011 / 1000) (11341 / 125) (-287963 / 500) (103657 / 500000) (4056267 / 1000) (81251 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1994569 / 500000) (157536557967 / 1000000) (81251 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1994569 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1994569 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell166 :
    ∀ t ∈ Set.Icc ((1913 / 16000) : ℝ) (383 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1270137293 / 1000000000) : ℝ) ≤ Real.exp (2 * (1913 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1913 / 16000)) (1270137293 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((383 / 3200) : ℝ)) ≤ (317613717 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (383 / 3200)) (317613717 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((632035713 / 4000) : ℝ) ≤ Real.exp (3 * (498767 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (498767 / 125000)) (632035713 / 4000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1913 / 16000) : ℝ) (383 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (498767 / 125000) (1995631 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1913 / 16000) (383 / 3200) (1270137293 / 1000000000) (317613717 / 250000000) (498767 / 125000) (1995631 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1913 / 16000) (383 / 3200) (498767 / 125000) (1995631 / 500000) (39737 / 1000) (1989 / 50)
    (11271 / 125) (45443 / 500) (-575927 / 1000) (206849 / 1000000) (4060327 / 1000) (810081 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (498767 / 125000) (632035713 / 4000) (810081 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (498767 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (498767 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell167 :
    ∀ t ∈ Set.Icc ((383 / 3200) : ℝ) (1917 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1270454867 / 1000000000) : ℝ) ≤ Real.exp (2 * (383 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (383 / 3200)) (1270454867 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1917 / 16000) : ℝ)) ≤ (635386261 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1917 / 16000)) (635386261 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((6339289579 / 40000) : ℝ) ≤ Real.exp (3 * (3991133 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3991133 / 1000000)) (6339289579 / 40000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((383 / 3200) : ℝ) (1917 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3991133 / 1000000) (3992259 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (383 / 3200) (1917 / 16000) (1270454867 / 1000000000) (635386261 / 500000000) (3991133 / 1000000) (3992259 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (383 / 3200) (1917 / 16000) (3991133 / 1000000) (3992259 / 1000000) (39763 / 1000) (19903 / 500)
    (3613 / 40) (91043 / 1000) (-575927 / 1000) (103193 / 500000) (812877 / 200) (1615323 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3991133 / 1000000) (6339289579 / 40000) (1615323 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3991133 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3991133 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell168 :
    ∀ t ∈ Set.Icc ((1917 / 16000) : ℝ) (1919 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1270772521 / 1000000000) : ℝ) ≤ Real.exp (2 * (1917 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1917 / 16000)) (1270772521 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1919 / 16000) : ℝ)) ≤ (254218051 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1919 / 16000)) (254218051 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((158957445357 / 1000000) : ℝ) ≤ Real.exp (3 * (3992131 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3992131 / 1000000)) (158957445357 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1917 / 16000) : ℝ) (1919 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3992131 / 1000000) (1996629 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1917 / 16000) (1919 / 16000) (1270772521 / 1000000000) (254218051 / 200000000) (3992131 / 1000000) (1996629 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1917 / 16000) (1919 / 16000) (3992131 / 1000000) (1996629 / 500000) (9947 / 250) (4979 / 125)
    (45241 / 500) (45601 / 500) (-575921 / 1000) (51481 / 250000) (813691 / 200) (805247 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3992131 / 1000000) (158957445357 / 1000000) (805247 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3992131 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3992131 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell169 :
    ∀ t ∈ Set.Icc ((1919 / 16000) : ℝ) (1921 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((635545127 / 500000000) : ℝ) ≤ Real.exp (2 * (1919 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1919 / 16000)) (635545127 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1921 / 16000) : ℝ)) ≤ (1271408067 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1921 / 16000)) (1271408067 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((159434554431 / 1000000) : ℝ) ≤ Real.exp (3 * (399313 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (399313 / 100000)) (159434554431 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1919 / 16000) : ℝ) (1921 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (399313 / 100000) (249641 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1919 / 16000) (1921 / 16000) (635545127 / 500000000) (1271408067 / 1000000000) (399313 / 100000) (249641 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1919 / 16000) (1921 / 16000) (399313 / 100000) (249641 / 62500) (19907 / 500) (19929 / 500)
    (2266 / 25) (91359 / 1000) (-287963 / 500) (205461 / 1000000) (1018131 / 250) (64227 / 40000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (399313 / 100000) (159434554431 / 1000000) (64227 / 40000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (399313 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (399313 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell170 :
    ∀ t ∈ Set.Icc ((1921 / 16000) : ℝ) (1923 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((635704033 / 500000000) : ℝ) ≤ Real.exp (2 * (1921 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1921 / 16000)) (635704033 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1923 / 16000) : ℝ)) ≤ (1271725959 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1923 / 16000)) (1271725959 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((799563079 / 5000) : ℝ) ≤ Real.exp (3 * (249633 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (249633 / 62500)) (799563079 / 5000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1921 / 16000) : ℝ) (1923 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (249633 / 62500) (799051 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1921 / 16000) (1923 / 16000) (635704033 / 500000000) (1271725959 / 1000000000) (249633 / 62500) (799051 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1921 / 16000) (1923 / 16000) (249633 / 62500) (799051 / 200000) (996 / 25) (9971 / 250)
    (45399 / 500) (45759 / 500) (-287959 / 500) (205001 / 1000000) (20383 / 5) (12807 / 8000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (249633 / 62500) (799563079 / 5000) (12807 / 8000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (249633 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (249633 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell171 :
    ∀ t ∈ Set.Icc ((1923 / 16000) : ℝ) (77 / 640), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((635862979 / 500000000) : ℝ) ≤ Real.exp (2 * (1923 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1923 / 16000)) (635862979 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((77 / 640) : ℝ)) ≤ (127204393 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (77 / 640)) (127204393 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((160392591799 / 1000000) : ℝ) ≤ Real.exp (3 * (3995127 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3995127 / 1000000)) (160392591799 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1923 / 16000) : ℝ) (77 / 640),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3995127 / 1000000) (1998127 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1923 / 16000) (77 / 640) (635862979 / 500000000) (127204393 / 100000000) (3995127 / 1000000) (1998127 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1923 / 16000) (77 / 640) (3995127 / 1000000) (1998127 / 500000) (19933 / 500) (3991 / 100)
    (22739 / 250) (22919 / 250) (-143979 / 250) (204541 / 1000000) (2040339 / 500) (399021 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3995127 / 1000000) (160392591799 / 1000000) (399021 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3995127 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3995127 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell172 :
    ∀ t ∈ Set.Icc ((77 / 640) : ℝ) (1927 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1272043929 / 1000000000) : ℝ) ≤ Real.exp (2 * (77 / 640)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (77 / 640)) (1272043929 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1927 / 16000) : ℝ)) ≤ (1272361981 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1927 / 16000)) (1272361981 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32174801687 / 200000) : ℝ) ≤ Real.exp (3 * (1998063 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1998063 / 500000)) (32174801687 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((77 / 640) : ℝ) (1927 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1998063 / 500000) (3997253 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (77 / 640) (1927 / 16000) (1272043929 / 1000000000) (1272361981 / 1000000000) (1998063 / 500000) (3997253 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (77 / 640) (1927 / 16000) (1998063 / 500000) (3997253 / 1000000) (9973 / 250) (4992 / 125)
    (45557 / 500) (45917 / 500) (-575913 / 1000) (102041 / 500000) (102119 / 25) (397827 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1998063 / 500000) (32174801687 / 200000) (397827 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1998063 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1998063 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell173 :
    ∀ t ∈ Set.Icc ((1927 / 16000) : ℝ) (1929 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((63618099 / 50000000) : ℝ) ≤ Real.exp (2 * (1927 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1927 / 16000)) (63618099 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1929 / 16000) : ℝ)) ≤ (1272680111 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1929 / 16000)) (1272680111 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((80678435017 / 500000) : ℝ) ≤ Real.exp (3 * (31977 / 8000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (31977 / 8000)) (80678435017 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1927 / 16000) : ℝ) (1929 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (31977 / 8000) (999563 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1927 / 16000) (1929 / 16000) (63618099 / 50000000) (1272680111 / 1000000000) (31977 / 8000) (999563 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1927 / 16000) (1929 / 16000) (31977 / 8000) (999563 / 250000) (19959 / 500) (19981 / 500)
    (91273 / 1000) (91993 / 1000) (-575909 / 1000) (25453 / 125000) (817769 / 200) (793273 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (31977 / 8000) (80678435017 / 500000) (793273 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (31977 / 8000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (31977 / 8000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell174 :
    ∀ t ∈ Set.Icc ((1929 / 16000) : ℝ) (1931 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((127268011 / 100000000) : ℝ) ≤ Real.exp (2 * (1929 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1929 / 16000)) (127268011 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1931 / 16000) : ℝ)) ≤ (1272998321 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1931 / 16000)) (1272998321 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((161841180931 / 1000000) : ℝ) ≤ Real.exp (3 * (999531 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (999531 / 250000)) (161841180931 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1929 / 16000) : ℝ) (1931 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (999531 / 250000) (999813 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1929 / 16000) (1931 / 16000) (127268011 / 100000000) (1272998321 / 1000000000) (999531 / 250000) (999813 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1929 / 16000) (1931 / 16000) (999531 / 250000) (999813 / 250000) (4993 / 125) (9997 / 250)
    (91431 / 1000) (11519 / 125) (-575899 / 1000) (203167 / 1000000) (2046469 / 500) (790899 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (999531 / 250000) (161841180931 / 1000000) (790899 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (999531 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (999531 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell175 :
    ∀ t ∈ Set.Icc ((1931 / 16000) : ℝ) (1933 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((15912479 / 12500000) : ℝ) ≤ Real.exp (2 * (1931 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1931 / 16000)) (15912479 / 12500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1933 / 16000) : ℝ)) ≤ (127331661 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1933 / 16000)) (127331661 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((162327432459 / 1000000) : ℝ) ≤ Real.exp (3 * (999781 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (999781 / 250000)) (162327432459 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1931 / 16000) : ℝ) (1933 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (999781 / 250000) (1000063 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1931 / 16000) (1933 / 16000) (15912479 / 12500000) (127331661 / 100000000) (999781 / 250000) (1000063 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1931 / 16000) (1933 / 16000) (999781 / 250000) (1000063 / 250000) (3997 / 100) (20007 / 500)
    (9159 / 100) (92311 / 1000) (-575893 / 1000) (20271 / 100000) (4097033 / 1000) (78853 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (999781 / 250000) (162327432459 / 1000000) (78853 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (999781 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (999781 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell176 :
    ∀ t ∈ Set.Icc ((1933 / 16000) : ℝ) (387 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1273316609 / 1000000000) : ℝ) ≤ Real.exp (2 * (1933 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1933 / 16000)) (1273316609 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((387 / 3200) : ℝ)) ≤ (1273634979 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (387 / 3200)) (1273634979 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((162815144923 / 1000000) : ℝ) ≤ Real.exp (3 * (1000031 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1000031 / 250000)) (162815144923 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1933 / 16000) : ℝ) (387 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1000031 / 250000) (1000313 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1933 / 16000) (387 / 3200) (1273316609 / 1000000000) (1273634979 / 1000000000) (1000031 / 250000) (1000313 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1933 / 16000) (387 / 3200) (1000031 / 250000) (1000313 / 250000) (9999 / 250) (1001 / 25)
    (22937 / 250) (9247 / 100) (-575887 / 1000) (101127 / 500000) (4101131 / 1000) (98271 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1000031 / 250000) (162815144923 / 1000000) (98271 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1000031 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1000031 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell177 :
    ∀ t ∈ Set.Icc ((387 / 3200) : ℝ) (1937 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((636817489 / 500000000) : ℝ) ≤ Real.exp (2 * (387 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (387 / 3200)) (636817489 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1937 / 16000) : ℝ)) ≤ (318488357 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1937 / 16000)) (318488357 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((163304322713 / 1000000) : ℝ) ≤ Real.exp (3 * (1000281 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1000281 / 250000)) (163304322713 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((387 / 3200) : ℝ) (1937 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1000281 / 250000) (4002253 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (387 / 3200) (1937 / 16000) (636817489 / 500000000) (318488357 / 250000000) (1000281 / 250000) (4002253 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (387 / 3200) (1937 / 16000) (1000281 / 250000) (4002253 / 1000000) (20011 / 500) (20033 / 500)
    (91907 / 1000) (9263 / 100) (-4607 / 8) (1009 / 5000) (4105237 / 1000) (783813 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1000281 / 250000) (163304322713 / 1000000) (783813 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1000281 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1000281 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell178 :
    ∀ t ∈ Set.Icc ((1937 / 16000) : ℝ) (1941 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1273953427 / 1000000000) : ℝ) ≤ Real.exp (2 * (1937 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1937 / 16000)) (1273953427 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1941 / 16000) : ℝ)) ≤ (318647641 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1941 / 16000)) (318647641 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((20474371279 / 125000) : ℝ) ≤ Real.exp (3 * (1000531 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1000531 / 250000)) (20474371279 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1937 / 16000) : ℝ) (1941 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1000531 / 250000) (2002127 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1937 / 16000) (1941 / 16000) (1273953427 / 1000000000) (318647641 / 250000000) (1000531 / 250000) (2002127 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1937 / 16000) (1941 / 16000) (1000531 / 250000) (2002127 / 500000) (20021 / 500) (10031 / 250)
    (45913 / 500) (9319 / 100) (-570433 / 1000) (201497 / 1000000) (4113453 / 1000) (156293 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1000531 / 250000) (20474371279 / 125000) (156293 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1000531 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1000531 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell179 :
    ∀ t ∈ Set.Icc ((1941 / 16000) : ℝ) (389 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1274590563 / 1000000000) : ℝ) ≤ Real.exp (2 * (1941 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1941 / 16000)) (1274590563 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((389 / 3200) : ℝ)) ≤ (637614009 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (389 / 3200)) (637614009 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((82390840409 / 500000) : ℝ) ≤ Real.exp (3 * (2002063 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2002063 / 500000)) (82390840409 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1941 / 16000) : ℝ) (389 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2002063 / 500000) (4006257 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1941 / 16000) (389 / 3200) (1274590563 / 1000000000) (637614009 / 500000000) (2002063 / 500000) (4006257 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1941 / 16000) (389 / 3200) (2002063 / 500000) (4006257 / 1000000) (20047 / 500) (5022 / 125)
    (18429 / 200) (9351 / 100) (-142601 / 250) (200591 / 1000000) (4121689 / 1000) (1553571 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2002063 / 500000) (82390840409 / 500000) (1553571 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2002063 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2002063 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityExpCompact_cellsBatch008 :
    ∀ t ∈ Set.Icc ((1901 / 16000) : ℝ) (389 / 3200),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell160
      hpThetaDensityExpCompact_cell161)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell162
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell163
      hpThetaDensityExpCompact_cell164)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell165
      hpThetaDensityExpCompact_cell166)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell167
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell168
      hpThetaDensityExpCompact_cell169))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell170
      hpThetaDensityExpCompact_cell171)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell172
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell173
      hpThetaDensityExpCompact_cell174)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell175
      hpThetaDensityExpCompact_cell176)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell177
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell178
      hpThetaDensityExpCompact_cell179)))))

#print axioms hpThetaDensityExpCompact_cellsBatch008
end HodgeProofHP
