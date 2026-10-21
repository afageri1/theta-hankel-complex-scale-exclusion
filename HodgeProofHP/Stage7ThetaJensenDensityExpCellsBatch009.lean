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
theorem hpThetaDensityExpCompact_cell180 :
    ∀ t ∈ Set.Icc ((389 / 3200) : ℝ) (1949 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1275228017 / 1000000000) : ℝ) ≤ Real.exp (2 * (389 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (389 / 3200)) (1275228017 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1949 / 16000) : ℝ)) ≤ (19935403 / 15625000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1949 / 16000)) (19935403 / 15625000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((33154867077 / 200000) : ℝ) ≤ Real.exp (3 * (250383 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (250383 / 62500)) (33154867077 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((389 / 3200) : ℝ) (1949 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (250383 / 62500) (200413 / 50000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (389 / 3200) (1949 / 16000) (1275228017 / 1000000000) (19935403 / 15625000) (250383 / 62500) (200413 / 50000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (389 / 3200) (1949 / 16000) (250383 / 62500) (200413 / 50000) (20073 / 500) (10057 / 250)
    (11558 / 125) (93831 / 1000) (-142593 / 250) (199689 / 1000000) (2064969 / 500) (386067 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (250383 / 62500) (33154867077 / 200000) (386067 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (250383 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (250383 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell181 :
    ∀ t ∈ Set.Icc ((1949 / 16000) : ℝ) (1953 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1275865791 / 1000000000) : ℝ) ≤ Real.exp (2 * (1949 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1949 / 16000)) (1275865791 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1953 / 16000) : ℝ)) ≤ (319125971 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1953 / 16000)) (319125971 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((166773970381 / 1000000) : ℝ) ≤ Real.exp (3 * (1002033 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1002033 / 250000)) (166773970381 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1949 / 16000) : ℝ) (1953 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1002033 / 250000) (802053 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1949 / 16000) (1953 / 16000) (1275865791 / 1000000000) (319125971 / 250000000) (1002033 / 250000) (802053 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1949 / 16000) (1953 / 16000) (1002033 / 250000) (802053 / 200000) (20099 / 500) (40281 / 1000)
    (11598 / 125) (94153 / 1000) (-71292 / 125) (198791 / 1000000) (517276 / 125) (383753 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1002033 / 250000) (166773970381 / 1000000) (383753 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1002033 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1002033 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell182 :
    ∀ t ∈ Set.Icc ((1953 / 16000) : ℝ) (1957 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1276503883 / 1000000000) : ℝ) ≤ Real.exp (2 * (1953 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1953 / 16000)) (1276503883 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1957 / 16000) : ℝ)) ≤ (159642787 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1957 / 16000)) (159642787 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((167779633249 / 1000000) : ℝ) ≤ Real.exp (3 * (501267 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (501267 / 125000)) (167779633249 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1953 / 16000) : ℝ) (1957 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (501267 / 125000) (4012271 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1953 / 16000) (1957 / 16000) (1276503883 / 1000000000) (159642787 / 125000000) (501267 / 125000) (4012271 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1953 / 16000) (1957 / 16000) (501267 / 125000) (4012271 / 1000000) (40251 / 1000) (40333 / 1000)
    (11638 / 125) (3779 / 40) (-570293 / 1000) (24737 / 125000) (2073247 / 500) (1525811 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (501267 / 125000) (167779633249 / 1000000) (1525811 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (501267 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (501267 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell183 :
    ∀ t ∈ Set.Icc ((1957 / 16000) : ℝ) (1961 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((255428459 / 200000000) : ℝ) ≤ Real.exp (2 * (1957 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1957 / 16000)) (255428459 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1961 / 16000) : ℝ)) ≤ (638890513 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1961 / 16000)) (638890513 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((168792373087 / 1000000) : ℝ) ≤ Real.exp (3 * (2006071 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2006071 / 500000)) (168792373087 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1957 / 16000) : ℝ) (1961 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2006071 / 500000) (4014277 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1957 / 16000) (1961 / 16000) (255428459 / 200000000) (638890513 / 500000000) (2006071 / 500000) (4014277 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1957 / 16000) (1961 / 16000) (2006071 / 500000) (4014277 / 1000000) (40303 / 1000) (8077 / 200)
    (46713 / 500) (47399 / 500) (-570257 / 1000) (49251 / 250000) (4154793 / 1000) (1516657 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2006071 / 500000) (168792373087 / 1000000) (1516657 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2006071 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2006071 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell184 :
    ∀ t ∈ Set.Icc ((1961 / 16000) : ℝ) (393 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((51111241 / 40000000) : ℝ) ≤ Real.exp (2 * (1961 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1961 / 16000)) (51111241 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((393 / 3200) : ℝ)) ≤ (1278420077 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (393 / 3200)) (1278420077 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((169811735367 / 1000000) : ℝ) ≤ Real.exp (3 * (4014149 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4014149 / 1000000)) (169811735367 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1961 / 16000) : ℝ) (393 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4014149 / 1000000) (803257 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1961 / 16000) (393 / 3200) (51111241 / 40000000) (1278420077 / 1000000000) (4014149 / 1000000) (803257 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1961 / 16000) (393 / 3200) (4014149 / 1000000) (803257 / 200000) (8071 / 200) (20219 / 500)
    (23437 / 250) (47561 / 500) (-570213 / 1000) (39223 / 200000) (520389 / 125) (47111 / 31250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4014149 / 1000000) (169811735367 / 1000000) (47111 / 31250000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4014149 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4014149 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell185 :
    ∀ t ∈ Set.Icc ((393 / 3200) : ℝ) (1969 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((319605019 / 250000000) : ℝ) ≤ Real.exp (2 * (393 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (393 / 3200)) (319605019 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1969 / 16000) : ℝ)) ≤ (639529723 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1969 / 16000)) (639529723 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((34167450741 / 200000) : ℝ) ≤ Real.exp (3 * (1004039 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1004039 / 250000)) (34167450741 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((393 / 3200) : ℝ) (1969 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1004039 / 250000) (2009147 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (393 / 3200) (1969 / 16000) (319605019 / 250000000) (639529723 / 500000000) (1004039 / 250000) (2009147 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (393 / 3200) (1969 / 16000) (1004039 / 250000) (2009147 / 500000) (5051 / 125) (4049 / 100)
    (9407 / 100) (95447 / 1000) (-14254 / 25) (19523 / 100000) (521431 / 125) (1498503 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1004039 / 250000) (34167450741 / 200000) (1498503 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1004039 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1004039 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell186 :
    ∀ t ∈ Set.Icc ((1969 / 16000) : ℝ) (1973 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((255811889 / 200000000) : ℝ) ≤ Real.exp (2 * (1969 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1969 / 16000)) (255811889 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1973 / 16000) : ℝ)) ≤ (19995299 / 15625000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1973 / 16000)) (19995299 / 15625000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((85934998247 / 500000) : ℝ) ≤ Real.exp (3 * (803633 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (803633 / 200000)) (85934998247 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1969 / 16000) : ℝ) (1973 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (803633 / 200000) (4020303 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1969 / 16000) (1973 / 16000) (255811889 / 200000000) (19995299 / 15625000) (803633 / 200000) (4020303 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1969 / 16000) (1973 / 16000) (803633 / 200000) (4020303 / 1000000) (2023 / 50) (40543 / 1000)
    (47197 / 500) (23943 / 250) (-142529 / 250) (48587 / 250000) (4179797 / 1000) (744749 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (803633 / 200000) (85934998247 / 500000) (744749 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (803633 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (803633 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell187 :
    ∀ t ∈ Set.Icc ((1973 / 16000) : ℝ) (1977 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((255939827 / 200000000) : ℝ) ≤ Real.exp (2 * (1973 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1973 / 16000)) (255939827 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1977 / 16000) : ℝ)) ≤ (640169573 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1977 / 16000)) (640169573 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8645449119 / 50000) : ℝ) ≤ Real.exp (3 * (2010087 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2010087 / 500000)) (8645449119 / 50000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1973 / 16000) : ℝ) (1977 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2010087 / 500000) (2011157 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1973 / 16000) (1977 / 16000) (255939827 / 200000000) (640169573 / 500000000) (2010087 / 500000) (2011157 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1973 / 16000) (1977 / 16000) (2010087 / 500000) (2011157 / 500000) (40513 / 1000) (8119 / 200)
    (47359 / 500) (48049 / 500) (-570057 / 1000) (193471 / 1000000) (2094083 / 500) (370137 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2010087 / 500000) (8645449119 / 50000) (370137 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2010087 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2010087 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell188 :
    ∀ t ∈ Set.Icc ((1977 / 16000) : ℝ) (1981 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((256067829 / 200000000) : ℝ) ≤ Real.exp (2 * (1977 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1977 / 16000)) (256067829 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1981 / 16000) : ℝ)) ≤ (51239179 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1981 / 16000)) (51239179 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((173955292831 / 1000000) : ℝ) ≤ Real.exp (3 * (804437 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (804437 / 200000)) (173955292831 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1977 / 16000) : ℝ) (1981 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (804437 / 200000) (2012163 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1977 / 16000) (1981 / 16000) (256067829 / 200000000) (51239179 / 40000000) (804437 / 200000) (2012163 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1977 / 16000) (1981 / 16000) (804437 / 200000) (2012163 / 500000) (8113 / 200) (5081 / 125)
    (95043 / 1000) (12053 / 125) (-570001 / 1000) (48149 / 250000) (524569 / 125) (1471643 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (804437 / 200000) (173955292831 / 1000000) (1471643 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (804437 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (804437 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell189 :
    ∀ t ∈ Set.Icc ((1981 / 16000) : ℝ) (397 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((640489737 / 500000000) : ℝ) ≤ Real.exp (2 * (1981 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1981 / 16000)) (640489737 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((397 / 3200) : ℝ)) ≤ (10252961 / 8000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (397 / 3200)) (10252961 / 8000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((175008459737 / 1000000) : ℝ) ≤ Real.exp (3 * (4024197 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4024197 / 1000000)) (175008459737 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1981 / 16000) : ℝ) (397 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4024197 / 1000000) (2013169 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1981 / 16000) (397 / 3200) (640489737 / 500000000) (10252961 / 8000000) (4024197 / 1000000) (2013169 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1981 / 16000) (397 / 3200) (4024197 / 1000000) (2013169 / 500000) (20309 / 500) (40701 / 1000)
    (11921 / 125) (96751 / 1000) (-569947 / 1000) (47931 / 250000) (4204951 / 1000) (1462787 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4024197 / 1000000) (175008459737 / 1000000) (1462787 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4024197 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4024197 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell190 :
    ∀ t ∈ Set.Icc ((397 / 3200) : ℝ) (1989 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((320405031 / 250000000) : ℝ) ≤ Real.exp (2 * (397 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (397 / 3200)) (320405031 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1989 / 16000) : ℝ)) ≤ (256452219 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1989 / 16000)) (256452219 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((22008500343 / 125000) : ℝ) ≤ Real.exp (3 * (4026209 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4026209 / 1000000)) (22008500343 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((397 / 3200) : ℝ) (1989 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4026209 / 1000000) (62943 / 15625) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (397 / 3200) (1989 / 16000) (320405031 / 250000000) (256452219 / 200000000) (4026209 / 1000000) (62943 / 15625) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (397 / 3200) (1989 / 16000) (4026209 / 1000000) (62943 / 15625) (40671 / 1000) (20377 / 500)
    (47847 / 500) (2427 / 25) (-14247 / 25) (23857 / 125000) (4213371 / 1000) (45437 / 31250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4026209 / 1000000) (22008500343 / 125000) (45437 / 31250000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4026209 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4026209 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell191 :
    ∀ t ∈ Set.Icc ((1989 / 16000) : ℝ) (1993 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((641130547 / 500000000) : ℝ) ≤ Real.exp (2 * (1989 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1989 / 16000)) (641130547 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1993 / 16000) : ℝ)) ≤ (641451193 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1993 / 16000)) (641451193 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((177135023257 / 1000000) : ℝ) ≤ Real.exp (3 * (4028223 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4028223 / 1000000)) (177135023257 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1989 / 16000) : ℝ) (1993 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4028223 / 1000000) (4030367 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1989 / 16000) (1993 / 16000) (641130547 / 500000000) (641451193 / 500000000) (4028223 / 1000000) (4030367 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1989 / 16000) (1993 / 16000) (4028223 / 1000000) (4030367 / 1000000) (10181 / 250) (40807 / 1000)
    (96021 / 1000) (12176 / 125) (-284907 / 500) (23749 / 125000) (4221807 / 1000) (722613 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4028223 / 1000000) (177135023257 / 1000000) (722613 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4028223 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4028223 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell192 :
    ∀ t ∈ Set.Icc ((1993 / 16000) : ℝ) (1997 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((256580477 / 200000000) : ℝ) ≤ Real.exp (2 * (1993 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1993 / 16000)) (256580477 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1997 / 16000) : ℝ)) ≤ (641771999 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1997 / 16000)) (641771999 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((89104255091 / 500000) : ℝ) ≤ Real.exp (3 * (4030237 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4030237 / 1000000)) (89104255091 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1993 / 16000) : ℝ) (1997 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4030237 / 1000000) (2016191 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1993 / 16000) (1997 / 16000) (256580477 / 200000000) (641771999 / 500000000) (4030237 / 1000000) (2016191 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1993 / 16000) (1997 / 16000) (4030237 / 1000000) (2016191 / 500000) (5097 / 125) (40859 / 1000)
    (96349 / 1000) (48869 / 500) (-284873 / 500) (18913 / 100000) (4230257 / 1000) (35913 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4030237 / 1000000) (89104255091 / 500000) (35913 / 25000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4030237 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4030237 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell193 :
    ∀ t ∈ Set.Icc ((1997 / 16000) : ℝ) (2001 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1283543997 / 1000000000) : ℝ) ≤ Real.exp (2 * (1997 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1997 / 16000)) (1283543997 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2001 / 16000) : ℝ)) ≤ (128418593 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2001 / 16000)) (128418593 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4482239461 / 25000) : ℝ) ≤ Real.exp (3 * (4032253 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4032253 / 1000000)) (4482239461 / 25000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1997 / 16000) : ℝ) (2001 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4032253 / 1000000) (4034399 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1997 / 16000) (2001 / 16000) (1283543997 / 1000000000) (128418593 / 100000000) (4032253 / 1000000) (4034399 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1997 / 16000) (2001 / 16000) (4032253 / 1000000) (4034399 / 1000000) (40829 / 1000) (5114 / 125)
    (96677 / 1000) (24517 / 250) (-22787 / 40) (11767 / 62500) (4238727 / 1000) (713929 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4032253 / 1000000) (4482239461 / 25000) (713929 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4032253 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4032253 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell194 :
    ∀ t ∈ Set.Icc ((2001 / 16000) : ℝ) (401 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1284185929 / 1000000000) : ℝ) ≤ Real.exp (2 * (2001 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2001 / 16000)) (1284185929 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((401 / 3200) : ℝ)) ≤ (160603523 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (401 / 3200)) (160603523 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1803777459 / 10000) : ℝ) ≤ Real.exp (3 * (403427 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (403427 / 100000)) (1803777459 / 10000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2001 / 16000) : ℝ) (401 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (403427 / 100000) (4036417 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2001 / 16000) (401 / 3200) (1284185929 / 1000000000) (160603523 / 125000000) (403427 / 100000) (4036417 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2001 / 16000) (401 / 3200) (403427 / 100000) (4036417 / 1000000) (20441 / 500) (20483 / 500)
    (48503 / 500) (98399 / 1000) (-2848 / 5) (187417 / 1000000) (2123607 / 500) (354811 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (403427 / 100000) (1803777459 / 10000) (354811 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (403427 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (403427 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell195 :
    ∀ t ∈ Set.Icc ((401 / 3200) : ℝ) (2009 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1284828183 / 1000000000) : ℝ) ≤ Real.exp (2 * (401 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (401 / 3200)) (1284828183 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2009 / 16000) : ℝ)) ≤ (1285470759 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2009 / 16000)) (1285470759 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((181472517781 / 1000000) : ℝ) ≤ Real.exp (3 * (4036287 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4036287 / 1000000)) (181472517781 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((401 / 3200) : ℝ) (2009 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4036287 / 1000000) (807687 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (401 / 3200) (2009 / 16000) (1284828183 / 1000000000) (1285470759 / 1000000000) (4036287 / 1000000) (807687 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (401 / 3200) (2009 / 16000) (4036287 / 1000000) (807687 / 200000) (8187 / 200) (41019 / 1000)
    (12167 / 125) (9873 / 100) (-569523 / 1000) (93283 / 500000) (2127857 / 500) (705341 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4036287 / 1000000) (181472517781 / 1000000) (705341 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4036287 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4036287 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell196 :
    ∀ t ∈ Set.Icc ((2009 / 16000) : ℝ) (2013 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((642735379 / 500000000) : ℝ) ≤ Real.exp (2 * (2009 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2009 / 16000)) (642735379 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2013 / 16000) : ℝ)) ≤ (257222731 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2013 / 16000)) (257222731 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((18257502961 / 100000) : ℝ) ≤ Real.exp (3 * (2019153 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2019153 / 500000)) (18257502961 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2009 / 16000) : ℝ) (2013 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2019153 / 500000) (808091 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2009 / 16000) (2013 / 16000) (642735379 / 500000000) (257222731 / 200000000) (2019153 / 500000) (808091 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2009 / 16000) (2013 / 16000) (2019153 / 500000) (808091 / 200000) (10247 / 250) (5134 / 125)
    (97667 / 1000) (49531 / 500) (-284721 / 500) (92859 / 500000) (852847 / 200) (350541 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2019153 / 500000) (18257502961 / 100000) (350541 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2019153 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2019153 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell197 :
    ∀ t ∈ Set.Icc ((2013 / 16000) : ℝ) (2017 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((643056827 / 500000000) : ℝ) ≤ Real.exp (2 * (2013 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2013 / 16000)) (643056827 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2017 / 16000) : ℝ)) ≤ (160844609 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2017 / 16000)) (160844609 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((91842395313 / 500000) : ℝ) ≤ Real.exp (3 * (2020163 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2020163 / 500000)) (91842395313 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2013 / 16000) : ℝ) (2017 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2020163 / 500000) (1010619 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2013 / 16000) (2017 / 16000) (643056827 / 500000000) (160844609 / 125000000) (2020163 / 500000) (1010619 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2013 / 16000) (2017 / 16000) (2020163 / 500000) (1010619 / 250000) (20521 / 500) (329 / 8)
    (48999 / 500) (19879 / 200) (-569359 / 1000) (184873 / 1000000) (4272773 / 1000) (348423 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2020163 / 500000) (91842395313 / 500000) (348423 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2020163 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2020163 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell198 :
    ∀ t ∈ Set.Icc ((2017 / 16000) : ℝ) (2021 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1286756871 / 1000000000) : ℝ) ≤ Real.exp (2 * (2017 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2017 / 16000)) (1286756871 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2021 / 16000) : ℝ)) ≤ (321850103 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2021 / 16000)) (321850103 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((11550081073 / 62500) : ℝ) ≤ Real.exp (3 * (2021173 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2021173 / 500000)) (11550081073 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2017 / 16000) : ℝ) (2021 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2021173 / 500000) (2022249 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2017 / 16000) (2021 / 16000) (1286756871 / 1000000000) (321850103 / 250000000) (2021173 / 500000) (2022249 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2017 / 16000) (2021 / 16000) (2021173 / 500000) (2022249 / 500000) (8219 / 200) (20589 / 500)
    (98329 / 1000) (99729 / 1000) (-284633 / 500) (5751 / 31250) (535166 / 125) (173159 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2021173 / 500000) (11550081073 / 62500) (173159 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2021173 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2021173 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell199 :
    ∀ t ∈ Set.Icc ((2021 / 16000) : ℝ) (81 / 640), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1287400411 / 1000000000) : ℝ) ≤ Real.exp (2 * (2021 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2021 / 16000)) (1287400411 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((81 / 640) : ℝ)) ≤ (1288044273 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (81 / 640)) (1288044273 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((37185141157 / 200000) : ℝ) ≤ Real.exp (3 * (252773 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (252773 / 62500)) (37185141157 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2021 / 16000) : ℝ) (81 / 640),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (252773 / 62500) (101163 / 25000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2021 / 16000) (81 / 640) (1287400411 / 1000000000) (1288044273 / 1000000000) (252773 / 62500) (101163 / 25000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2021 / 16000) (81 / 640) (252773 / 62500) (101163 / 25000) (10287 / 250) (5154 / 125)
    (49331 / 500) (100063 / 1000) (-284591 / 500) (91597 / 500000) (536237 / 125) (275379 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (252773 / 62500) (37185141157 / 200000) (275379 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (252773 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (252773 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityExpCompact_cellsBatch009 :
    ∀ t ∈ Set.Icc ((389 / 3200) : ℝ) (81 / 640),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell180
      hpThetaDensityExpCompact_cell181)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell182
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell183
      hpThetaDensityExpCompact_cell184)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell185
      hpThetaDensityExpCompact_cell186)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell187
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell188
      hpThetaDensityExpCompact_cell189))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell190
      hpThetaDensityExpCompact_cell191)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell192
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell193
      hpThetaDensityExpCompact_cell194)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell195
      hpThetaDensityExpCompact_cell196)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell197
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell198
      hpThetaDensityExpCompact_cell199)))))

#print axioms hpThetaDensityExpCompact_cellsBatch009
end HodgeProofHP
