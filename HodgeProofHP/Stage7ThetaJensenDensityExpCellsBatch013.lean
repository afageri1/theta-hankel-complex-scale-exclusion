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
theorem hpThetaDensityExpCompact_cell260 :
    ∀ t ∈ Set.Icc ((453 / 3200) : ℝ) (2269 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((66363553 / 50000000) : ℝ) ≤ Real.exp (2 * (453 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (453 / 3200)) (66363553 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2269 / 16000) : ℝ)) ≤ (663967431 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2269 / 16000)) (663967431 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((270726160271 / 1000000) : ℝ) ≤ Real.exp (3 * (2084811 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2084811 / 500000)) (270726160271 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((453 / 3200) : ℝ) (2269 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2084811 / 500000) (4171841 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (453 / 3200) (2269 / 16000) (66363553 / 50000000) (663967431 / 500000000) (2084811 / 500000) (4171841 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (453 / 3200) (2269 / 16000) (2084811 / 500000) (4171841 / 1000000) (44511 / 1000) (223 / 5)
    (15044 / 125) (30467 / 250) (-557231 / 1000) (68933 / 500000) (4846531 / 1000) (189121 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2084811 / 500000) (270726160271 / 1000000) (189121 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2084811 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2084811 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell261 :
    ∀ t ∈ Set.Icc ((2269 / 16000) : ℝ) (2273 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1327934861 / 1000000000) : ℝ) ≤ Real.exp (2 * (2269 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2269 / 16000)) (1327934861 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2273 / 16000) : ℝ)) ≤ (332149749 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2273 / 16000)) (332149749 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((272424851609 / 1000000) : ℝ) ≤ Real.exp (3 * (4171707 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4171707 / 1000000)) (272424851609 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2269 / 16000) : ℝ) (2273 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4171707 / 1000000) (4173927 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2269 / 16000) (2273 / 16000) (1327934861 / 1000000000) (332149749 / 250000000) (4171707 / 1000000) (4173927 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2269 / 16000) (2273 / 16000) (4171707 / 1000000) (4173927 / 1000000) (5571 / 125) (44657 / 1000)
    (120731 / 1000) (122249 / 1000) (-556921 / 1000) (34303 / 250000) (607029 / 125) (939709 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4171707 / 1000000) (272424851609 / 1000000) (939709 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4171707 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4171707 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell262 :
    ∀ t ∈ Set.Icc ((2273 / 16000) : ℝ) (2277 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((265719799 / 200000000) : ℝ) ≤ Real.exp (2 * (2273 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2273 / 16000)) (265719799 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2277 / 16000) : ℝ)) ≤ (1329263461 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2277 / 16000)) (1329263461 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((137067511919 / 500000) : ℝ) ≤ Real.exp (3 * (4173793 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4173793 / 1000000)) (137067511919 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2273 / 16000) : ℝ) (2277 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4173793 / 1000000) (835203 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2273 / 16000) (2277 / 16000) (265719799 / 200000000) (1329263461 / 1000000000) (4173793 / 1000000) (835203 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2273 / 16000) (2277 / 16000) (4173793 / 1000000) (835203 / 200000) (22313 / 500) (22357 / 500)
    (121111 / 1000) (15329 / 125) (-278301 / 500) (136561 / 1000000) (4865957 / 1000) (933847 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4173793 / 1000000) (137067511919 / 500000) (933847 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4173793 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4173793 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell263 :
    ∀ t ∈ Set.Icc ((2277 / 16000) : ℝ) (2281 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((66463173 / 50000000) : ℝ) ≤ Real.exp (2 * (2277 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2277 / 16000)) (66463173 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2281 / 16000) : ℝ)) ≤ (1329928259 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2281 / 16000)) (1329928259 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((275857586889 / 1000000) : ℝ) ≤ Real.exp (3 * (4175881 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4175881 / 1000000)) (275857586889 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2277 / 16000) : ℝ) (2281 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4175881 / 1000000) (4178103 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2277 / 16000) (2281 / 16000) (66463173 / 50000000) (1329928259 / 1000000000) (4175881 / 1000000) (4178103 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2277 / 16000) (2281 / 16000) (4175881 / 1000000) (4178103 / 1000000) (44683 / 1000) (44771 / 1000)
    (121493 / 1000) (24603 / 200) (-556291 / 1000) (16989 / 125000) (609462 / 125) (58001 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4175881 / 1000000) (275857586889 / 1000000) (58001 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4175881 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4175881 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell264 :
    ∀ t ∈ Set.Icc ((2281 / 16000) : ℝ) (457 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((664964129 / 500000000) : ℝ) ≤ Real.exp (2 * (2281 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2281 / 16000)) (664964129 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((457 / 3200) : ℝ)) ≤ (133059339 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (457 / 3200)) (133059339 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((69397743453 / 250000) : ℝ) ≤ Real.exp (3 * (4177969 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4177969 / 1000000)) (69397743453 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2281 / 16000) : ℝ) (457 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4177969 / 1000000) (4180193 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2281 / 16000) (457 / 3200) (664964129 / 500000000) (133059339 / 100000000) (4177969 / 1000000) (4180193 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2281 / 16000) (457 / 3200) (4177969 / 1000000) (4180193 / 1000000) (2237 / 50) (44829 / 1000)
    (60937 / 500) (123399 / 1000) (-138991 / 250) (67633 / 500000) (4885459 / 1000) (922221 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4177969 / 1000000) (69397743453 / 250000) (922221 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4177969 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4177969 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell265 :
    ∀ t ∈ Set.Icc ((457 / 3200) : ℝ) (2289 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1330593389 / 1000000000) : ℝ) ≤ Real.exp (2 * (457 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (457 / 3200)) (1330593389 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2289 / 16000) : ℝ)) ≤ (1331258853 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2289 / 16000)) (1331258853 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((279336928627 / 1000000) : ℝ) ≤ Real.exp (3 * (4180059 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4180059 / 1000000)) (279336928627 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((457 / 3200) : ℝ) (2289 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4180059 / 1000000) (4182283 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (457 / 3200) (2289 / 16000) (1330593389 / 1000000000) (1331258853 / 1000000000) (4180059 / 1000000) (4182283 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (457 / 3200) (2289 / 16000) (4180059 / 1000000) (4182283 / 1000000) (44797 / 1000) (22443 / 500)
    (122257 / 1000) (123783 / 1000) (-111129 / 200) (67311 / 500000) (4895237 / 1000) (114557 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4180059 / 1000000) (279336928627 / 1000000) (114557 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4180059 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4180059 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell266 :
    ∀ t ∈ Set.Icc ((2289 / 16000) : ℝ) (2293 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((332814713 / 250000000) : ℝ) ≤ Real.exp (2 * (2289 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2289 / 16000)) (332814713 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2293 / 16000) : ℝ)) ≤ (1331924649 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2293 / 16000)) (1331924649 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((140546932419 / 500000) : ℝ) ≤ Real.exp (3 * (4182149 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4182149 / 1000000)) (140546932419 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2289 / 16000) : ℝ) (2293 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4182149 / 1000000) (1339 / 320) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2289 / 16000) (2293 / 16000) (332814713 / 250000000) (1331924649 / 1000000000) (4182149 / 1000000) (1339 / 320) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2289 / 16000) (2293 / 16000) (4182149 / 1000000) (1339 / 320) (8971 / 200) (5618 / 125)
    (122641 / 1000) (124169 / 1000) (-55531 / 100) (66991 / 500000) (4905039 / 1000) (113841 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4182149 / 1000000) (140546932419 / 500000) (113841 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4182149 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4182149 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell267 :
    ∀ t ∈ Set.Icc ((2293 / 16000) : ℝ) (2297 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((166490581 / 125000000) : ℝ) ≤ Real.exp (2 * (2293 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2293 / 16000)) (166490581 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2297 / 16000) : ℝ)) ≤ (1332590777 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2297 / 16000)) (1332590777 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((7071588717 / 25000) : ℝ) ≤ Real.exp (3 * (4184241 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4184241 / 1000000)) (7071588717 / 25000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2293 / 16000) : ℝ) (2297 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4184241 / 1000000) (1046617 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2293 / 16000) (2297 / 16000) (166490581 / 125000000) (1332590777 / 1000000000) (4184241 / 1000000) (1046617 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2293 / 16000) (2297 / 16000) (4184241 / 1000000) (1046617 / 250000) (5614 / 125) (45001 / 1000)
    (4921 / 40) (24911 / 200) (-69372 / 125) (4167 / 31250) (245743 / 50) (905031 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4184241 / 1000000) (7071588717 / 25000) (905031 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4184241 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4184241 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell268 :
    ∀ t ∈ Set.Icc ((2297 / 16000) : ℝ) (2301 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((166573847 / 125000000) : ℝ) ≤ Real.exp (2 * (2297 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2297 / 16000)) (166573847 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2301 / 16000) : ℝ)) ≤ (1333257239 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2301 / 16000)) (1333257239 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((142322186923 / 500000) : ℝ) ≤ Real.exp (3 * (4186333 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4186333 / 1000000)) (142322186923 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2297 / 16000) : ℝ) (2301 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4186333 / 1000000) (4188561 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2297 / 16000) (2301 / 16000) (166573847 / 125000000) (1333257239 / 1000000000) (4186333 / 1000000) (4188561 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2297 / 16000) (2301 / 16000) (4186333 / 1000000) (4188561 / 1000000) (4497 / 100) (45059 / 1000)
    (12341 / 100) (62471 / 500) (-554639 / 1000) (33177 / 250000) (615587 / 125) (112421 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4186333 / 1000000) (142322186923 / 500000) (112421 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4186333 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4186333 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell269 :
    ∀ t ∈ Set.Icc ((2301 / 16000) : ℝ) (461 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((666628619 / 500000000) : ℝ) ≤ Real.exp (2 * (2301 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2301 / 16000)) (666628619 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((461 / 3200) : ℝ)) ≤ (266784807 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (461 / 3200)) (266784807 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((286438129093 / 1000000) : ℝ) ≤ Real.exp (3 * (4188427 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4188427 / 1000000)) (286438129093 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2301 / 16000) : ℝ) (461 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4188427 / 1000000) (65479 / 15625) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2301 / 16000) (461 / 3200) (666628619 / 500000000) (266784807 / 200000000) (4188427 / 1000000) (65479 / 15625) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2301 / 16000) (461 / 3200) (4188427 / 1000000) (65479 / 15625) (45027 / 1000) (11279 / 250)
    (30949 / 250) (12533 / 100) (-277149 / 500) (5283 / 40000) (1233639 / 250) (111717 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4188427 / 1000000) (286438129093 / 1000000) (111717 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4188427 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4188427 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell270 :
    ∀ t ∈ Set.Icc ((461 / 3200) : ℝ) (2309 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((666962017 / 500000000) : ℝ) ≤ Real.exp (2 * (461 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (461 / 3200)) (666962017 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2309 / 16000) : ℝ)) ≤ (1334591163 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2309 / 16000)) (1334591163 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((72061013191 / 250000) : ℝ) ≤ Real.exp (3 * (2095261 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2095261 / 500000)) (72061013191 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((461 / 3200) : ℝ) (2309 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2095261 / 500000) (262047 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (461 / 3200) (2309 / 16000) (666962017 / 500000000) (1334591163 / 1000000000) (2095261 / 500000) (262047 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (461 / 3200) (2309 / 16000) (2095261 / 500000) (262047 / 62500) (9017 / 200) (22587 / 500)
    (124183 / 1000) (62859 / 500) (-69244 / 125) (26289 / 200000) (1236109 / 250) (888137 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2095261 / 500000) (72061013191 / 250000) (888137 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2095261 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2095261 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell271 :
    ∀ t ∈ Set.Icc ((2309 / 16000) : ℝ) (2313 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((667295581 / 500000000) : ℝ) ≤ Real.exp (2 * (2309 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2309 / 16000)) (667295581 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2313 / 16000) : ℝ)) ≤ (667629313 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2313 / 16000)) (667629313 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((145031116223 / 500000) : ℝ) ≤ Real.exp (3 * (2096309 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2096309 / 500000)) (145031116223 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2309 / 16000) : ℝ) (2313 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2096309 / 500000) (4194849 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2309 / 16000) (2313 / 16000) (667295581 / 500000000) (667629313 / 500000000) (2096309 / 500000) (4194849 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2309 / 16000) (2313 / 16000) (2096309 / 500000) (4194849 / 1000000) (45143 / 1000) (5654 / 125)
    (12457 / 100) (31527 / 250) (-553603 / 1000) (130817 / 1000000) (990867 / 200) (88257 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2096309 / 500000) (145031116223 / 500000) (88257 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2096309 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2096309 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell272 :
    ∀ t ∈ Set.Icc ((2313 / 16000) : ℝ) (2317 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((10682069 / 8000000) : ℝ) ≤ Real.exp (2 * (2313 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2313 / 16000)) (10682069 / 8000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2317 / 16000) : ℝ)) ≤ (667963211 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2317 / 16000)) (667963211 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((72972970179 / 250000) : ℝ) ≤ Real.exp (3 * (2097357 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2097357 / 500000)) (72972970179 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2313 / 16000) : ℝ) (2317 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2097357 / 500000) (4196947 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2313 / 16000) (2317 / 16000) (10682069 / 8000000) (667963211 / 500000000) (2097357 / 500000) (4196947 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2313 / 16000) (2317 / 16000) (2097357 / 500000) (4196947 / 1000000) (226 / 5) (4529 / 100)
    (62479 / 500) (63249 / 500) (-553243 / 1000) (8137 / 62500) (2482127 / 500) (438519 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2097357 / 500000) (72972970179 / 250000) (438519 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2097357 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2097357 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell273 :
    ∀ t ∈ Set.Icc ((2317 / 16000) : ℝ) (2321 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1335926421 / 1000000000) : ℝ) ≤ Real.exp (2 * (2317 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2317 / 16000)) (1335926421 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2321 / 16000) : ℝ)) ≤ (167074319 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2321 / 16000)) (167074319 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((73433708077 / 250000) : ℝ) ≤ Real.exp (3 * (1049203 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1049203 / 250000)) (73433708077 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2317 / 16000) : ℝ) (2321 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1049203 / 250000) (2099523 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2317 / 16000) (2321 / 16000) (1335926421 / 1000000000) (167074319 / 125000000) (1049203 / 250000) (2099523 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2317 / 16000) (2321 / 16000) (1049203 / 250000) (2099523 / 500000) (22629 / 500) (11337 / 250)
    (125347 / 1000) (126889 / 1000) (-110577 / 200) (129569 / 1000000) (621774 / 125) (174307 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1049203 / 250000) (73433708077 / 250000) (174307 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1049203 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1049203 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell274 :
    ∀ t ∈ Set.Icc ((2321 / 16000) : ℝ) (93 / 640), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1336594551 / 1000000000) : ℝ) ≤ Real.exp (2 * (2321 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2321 / 16000)) (1336594551 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((93 / 640) : ℝ)) ≤ (1337263017 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (93 / 640)) (1337263017 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((295590306633 / 1000000) : ℝ) ≤ Real.exp (3 * (4198911 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4198911 / 1000000)) (295590306633 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2321 / 16000) : ℝ) (93 / 640),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4198911 / 1000000) (2100573 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2321 / 16000) (93 / 640) (1336594551 / 1000000000) (1337263017 / 1000000000) (4198911 / 1000000) (2100573 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2321 / 16000) (93 / 640) (4198911 / 1000000) (2100573 / 500000) (11329 / 250) (22703 / 500)
    (125737 / 1000) (127281 / 1000) (-552523 / 1000) (128949 / 1000000) (99683 / 20) (54129 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4198911 / 1000000) (295590306633 / 1000000) (54129 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4198911 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4198911 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell275 :
    ∀ t ∈ Set.Icc ((93 / 640) : ℝ) (2329 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((167157877 / 125000000) : ℝ) ≤ Real.exp (2 * (93 / 640)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (93 / 640)) (167157877 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2329 / 16000) : ℝ)) ≤ (267586363 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2329 / 16000)) (267586363 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((7436459849 / 25000) : ℝ) ≤ Real.exp (3 * (4201011 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4201011 / 1000000)) (7436459849 / 25000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((93 / 640) : ℝ) (2329 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4201011 / 1000000) (4203247 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (93 / 640) (2329 / 16000) (167157877 / 125000000) (267586363 / 200000000) (4201011 / 1000000) (4203247 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (93 / 640) (2329 / 16000) (4201011 / 1000000) (4203247 / 1000000) (22687 / 500) (5683 / 125)
    (15766 / 125) (63837 / 500) (-552157 / 1000) (32083 / 250000) (624266 / 125) (1377 / 1600000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4201011 / 1000000) (7436459849 / 25000) (1377 / 1600000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4201011 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4201011 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell276 :
    ∀ t ∈ Set.Icc ((2329 / 16000) : ℝ) (2333 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((668965907 / 500000000) : ℝ) ≤ Real.exp (2 * (2329 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2329 / 16000)) (668965907 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2333 / 16000) : ℝ)) ≤ (1338600949 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2333 / 16000)) (1338600949 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((299339185243 / 1000000) : ℝ) ≤ Real.exp (3 * (525389 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (525389 / 125000)) (299339185243 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2329 / 16000) : ℝ) (2333 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (525389 / 125000) (4205349 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2329 / 16000) (2333 / 16000) (668965907 / 500000000) (1338600949 / 1000000000) (525389 / 125000) (4205349 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2329 / 16000) (2333 / 16000) (525389 / 125000) (4205349 / 1000000) (5679 / 125) (22761 / 500)
    (3163 / 25) (32017 / 250) (-551787 / 1000) (127717 / 1000000) (2502063 / 500) (427609 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (525389 / 125000) (299339185243 / 1000000) (427609 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (525389 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (525389 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell277 :
    ∀ t ∈ Set.Icc ((2333 / 16000) : ℝ) (2337 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((334650237 / 250000000) : ℝ) ≤ Real.exp (2 * (2333 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2333 / 16000)) (334650237 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2337 / 16000) : ℝ)) ≤ (83704401 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2337 / 16000)) (83704401 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((301232772127 / 1000000) : ℝ) ≤ Real.exp (3 * (2102607 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2102607 / 500000)) (301232772127 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2333 / 16000) : ℝ) (2337 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2102607 / 500000) (1051863 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2333 / 16000) (2337 / 16000) (334650237 / 250000000) (83704401 / 62500000) (2102607 / 500000) (1051863 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2333 / 16000) (2337 / 16000) (2102607 / 500000) (1051863 / 250000) (4549 / 100) (2279 / 50)
    (15864 / 125) (64231 / 500) (-551413 / 1000) (25421 / 200000) (5014143 / 1000) (424921 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2102607 / 500000) (301232772127 / 1000000) (424921 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2102607 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2102607 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell278 :
    ∀ t ∈ Set.Icc ((2337 / 16000) : ℝ) (2341 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((267854083 / 200000000) : ℝ) ≤ Real.exp (2 * (2337 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2337 / 16000)) (267854083 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2341 / 16000) : ℝ)) ≤ (1339940219 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2341 / 16000)) (1339940219 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((60628031273 / 200000) : ℝ) ≤ Real.exp (3 * (2103659 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2103659 / 500000)) (60628031273 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2337 / 16000) : ℝ) (2341 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2103659 / 500000) (4209557 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2337 / 16000) (2341 / 16000) (267854083 / 200000000) (1339940219 / 1000000000) (2103659 / 500000) (4209557 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2337 / 16000) (2341 / 16000) (2103659 / 500000) (4209557 / 1000000) (11387 / 250) (22819 / 500)
    (63653 / 500) (128857 / 1000) (-275517 / 500) (63247 / 500000) (1004837 / 200) (422247 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2103659 / 500000) (60628031273 / 200000) (422247 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2103659 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2103659 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell279 :
    ∀ t ∈ Set.Icc ((2341 / 16000) : ℝ) (469 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((669970109 / 500000000) : ℝ) ≤ Real.exp (2 * (2341 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2341 / 16000)) (669970109 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((469 / 3200) : ℝ)) ≤ (1340610357 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (469 / 3200)) (1340610357 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((12202384717 / 40000) : ℝ) ≤ Real.exp (3 * (2104711 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2104711 / 500000)) (12202384717 / 40000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2341 / 16000) : ℝ) (469 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2104711 / 500000) (2105831 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2341 / 16000) (469 / 3200) (669970109 / 500000000) (1340610357 / 1000000000) (2104711 / 500000) (2105831 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2341 / 16000) (469 / 3200) (2104711 / 500000) (2105831 / 500000) (22803 / 500) (5712 / 125)
    (1277 / 10) (129253 / 1000) (-137663 / 250) (125887 / 1000000) (2517121 / 500) (839181 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2104711 / 500000) (12202384717 / 40000) (839181 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2104711 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2104711 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityExpCompact_cellsBatch013 :
    ∀ t ∈ Set.Icc ((453 / 3200) : ℝ) (469 / 3200),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell260
      hpThetaDensityExpCompact_cell261)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell262
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell263
      hpThetaDensityExpCompact_cell264)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell265
      hpThetaDensityExpCompact_cell266)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell267
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell268
      hpThetaDensityExpCompact_cell269))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell270
      hpThetaDensityExpCompact_cell271)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell272
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell273
      hpThetaDensityExpCompact_cell274)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell275
      hpThetaDensityExpCompact_cell276)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell277
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell278
      hpThetaDensityExpCompact_cell279)))))

#print axioms hpThetaDensityExpCompact_cellsBatch013
end HodgeProofHP
