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
theorem hpThetaDensityUpperExpCompact_cell180 :
    ∀ t ∈ Set.Icc ((707 / 2000) : ℝ) (709 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((506974607 / 250000000) : ℝ) ≤ Real.exp (2 * (707 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (707 / 2000)) (506974607 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((709 / 2000) : ℝ)) ≤ (406391657 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (709 / 2000)) (406391657 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2484409864407 / 12500) : ℝ) ≤ Real.exp (3 * (3185321 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3185321 / 500000)) (2484409864407 / 12500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((707 / 2000) : ℝ) (709 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3185321 / 500000) (6383601 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (707 / 2000) (709 / 2000) (506974607 / 250000000) (406391657 / 200000000) (3185321 / 500000) (6383601 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (707 / 2000) (709 / 2000) (3185321 / 500000) (6383601 / 1000000) (62019 / 500) (62389 / 500)
    (117684 / 125) (38371 / 40) (819289 / 200) (337 / 500000) (3321184 / 125) (1289 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3185321 / 500000) (2484409864407 / 12500) (1289 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3185321 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3185321 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell181 :
    ∀ t ∈ Set.Icc ((709 / 2000) : ℝ) (711 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((507989571 / 250000000) : ℝ) ≤ Real.exp (2 * (709 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (709 / 2000)) (507989571 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((711 / 2000) : ℝ)) ≤ (509006567 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (711 / 2000)) (509006567 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((103239562346753 / 500000) : ℝ) ≤ Real.exp (3 * (1595849 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1595849 / 250000)) (103239562346753 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((709 / 2000) : ℝ) (711 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1595849 / 250000) (6396381 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (709 / 2000) (711 / 2000) (507989571 / 250000000) (509006567 / 250000000) (1595849 / 250000) (6396381 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (709 / 2000) (711 / 2000) (1595849 / 250000) (6396381 / 1000000) (31153 / 250) (25071 / 200)
    (237303 / 250) (96711 / 100) (520257 / 125) (163 / 250000) (26782881 / 1000) (31 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1595849 / 250000) (103239562346753 / 500000) (31 / 25000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1595849 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1595849 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell182 :
    ∀ t ∈ Set.Icc ((711 / 2000) : ℝ) (713 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2036026267 / 1000000000) : ℝ) ≤ Real.exp (2 * (711 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (711 / 2000)) (2036026267 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((713 / 2000) : ℝ)) ≤ (408020479 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (713 / 2000)) (408020479 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((26815230886529 / 125000) : ℝ) ≤ Real.exp (3 * (399761 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (399761 / 62500)) (26815230886529 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((711 / 2000) : ℝ) (713 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (399761 / 62500) (3204593 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (711 / 2000) (713 / 2000) (2036026267 / 1000000000) (408020479 / 200000000) (399761 / 62500) (3204593 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (711 / 2000) (713 / 2000) (399761 / 62500) (3204593 / 500000) (125189 / 1000) (62967 / 500)
    (957007 / 1000) (975001 / 1000) (211421 / 50) (79 / 125000) (13498997 / 500) (597 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (399761 / 62500) (26815230886529 / 125000) (597 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (399761 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (399761 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell183 :
    ∀ t ∈ Set.Icc ((713 / 2000) : ℝ) (143 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1020051197 / 500000000) : ℝ) ≤ Real.exp (2 * (713 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (713 / 2000)) (1020051197 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((143 / 400) : ℝ)) ≤ (2044186683 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (143 / 400)) (2044186683 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((222893822660473 / 1000000) : ℝ) ≤ Real.exp (3 * (6408981 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6408981 / 1000000)) (222893822660473 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((713 / 2000) : ℝ) (143 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6408981 / 1000000) (6422017 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (713 / 2000) (143 / 400) (1020051197 / 500000000) (2044186683 / 1000000000) (6408981 / 1000000) (6422017 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (713 / 2000) (143 / 400) (6408981 / 1000000) (6422017 / 1000000) (15721 / 125) (31629 / 250)
    (482429 / 500) (19659 / 20) (4295581 / 1000) (153 / 250000) (27214841 / 1000) (1149 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6408981 / 1000000) (222893822660473 / 1000000) (1149 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6408981 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6408981 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell184 :
    ∀ t ∈ Set.Icc ((143 / 400) : ℝ) (717 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1022093341 / 500000000) : ℝ) ≤ Real.exp (2 * (143 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (143 / 400)) (1022093341 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((717 / 2000) : ℝ)) ≤ (2048279147 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (717 / 2000)) (2048279147 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((7237806225689 / 31250) : ℝ) ≤ Real.exp (3 * (1605453 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1605453 / 250000)) (7237806225689 / 31250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((143 / 400) : ℝ) (717 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1605453 / 250000) (3217437 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (143 / 400) (717 / 2000) (1022093341 / 500000000) (2048279147 / 1000000000) (1605453 / 250000) (3217437 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (143 / 400) (717 / 2000) (1605453 / 250000) (3217437 / 500000) (126349 / 1000) (1271 / 10)
    (486383 / 500) (198191 / 200) (436353 / 100) (37 / 62500) (13716717 / 500) (553 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1605453 / 250000) (7237806225689 / 31250) (553 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1605453 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1605453 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell185 :
    ∀ t ∈ Set.Icc ((717 / 2000) : ℝ) (719 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1024139573 / 500000000) : ℝ) ≤ Real.exp (2 * (717 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (717 / 2000)) (1024139573 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((719 / 2000) : ℝ)) ≤ (410475961 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (719 / 2000)) (410475961 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((60170953973387 / 250000) : ℝ) ≤ Real.exp (3 * (1608667 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1608667 / 250000)) (60170953973387 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((717 / 2000) : ℝ) (719 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1608667 / 250000) (6447757 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (717 / 2000) (719 / 2000) (1024139573 / 500000000) (410475961 / 200000000) (1608667 / 250000) (6447757 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (717 / 2000) (719 / 2000) (1608667 / 250000) (6447757 / 1000000) (126933 / 1000) (127687 / 1000)
    (980729 / 1000) (999019 / 1000) (443229 / 100) (573 / 1000000) (27653789 / 1000) (133 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1608667 / 250000) (60170953973387 / 250000) (133 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1608667 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1608667 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell186 :
    ∀ t ∈ Set.Icc ((719 / 2000) : ℝ) (721 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((513094951 / 250000000) : ℝ) ≤ Real.exp (2 * (719 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (719 / 2000)) (513094951 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((721 / 2000) : ℝ)) ≤ (64265271 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (721 / 2000)) (64265271 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((25013269888661 / 100000) : ℝ) ≤ Real.exp (3 * (6447551 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6447551 / 1000000)) (25013269888661 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((719 / 2000) : ℝ) (721 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6447551 / 1000000) (1292133 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (719 / 2000) (721 / 2000) (513094951 / 250000000) (64265271 / 31250000) (6447551 / 1000000) (1292133 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (719 / 2000) (721 / 2000) (6447551 / 1000000) (1292133 / 200000) (127519 / 1000) (32069 / 250)
    (123594 / 125) (503569 / 500) (2250911 / 500) (111 / 200000) (27875899 / 1000) (2 / 1953125)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6447551 / 1000000) (25013269888661 / 100000) (2 / 1953125)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6447551 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6447551 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell187 :
    ∀ t ∈ Set.Icc ((721 / 2000) : ℝ) (723 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2056488671 / 1000000000) : ℝ) ≤ Real.exp (2 * (721 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (721 / 2000)) (2056488671 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((723 / 2000) : ℝ)) ≤ (412121153 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (723 / 2000)) (412121153 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((259971081478977 / 1000000) : ℝ) ≤ Real.exp (3 * (6460459 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6460459 / 1000000)) (259971081478977 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((721 / 2000) : ℝ) (723 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6460459 / 1000000) (4046 / 625) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (721 / 2000) (723 / 2000) (2056488671 / 1000000000) (412121153 / 200000000) (6460459 / 1000000) (4046 / 625) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (721 / 2000) (723 / 2000) (6460459 / 1000000) (4046 / 625) (32027 / 250) (32217 / 250)
    (99683 / 100) (507659 / 500) (4572199 / 1000) (537 / 1000000) (28099813 / 1000) (197 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6460459 / 1000000) (259971081478977 / 1000000) (197 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6460459 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6460459 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell188 :
    ∀ t ∈ Set.Icc ((723 / 2000) : ℝ) (29 / 80), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((515151441 / 250000000) : ℝ) ≤ Real.exp (2 * (723 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (723 / 2000)) (515151441 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((29 / 80) : ℝ)) ≤ (20647311 / 10000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (29 / 80)) (20647311 / 10000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((270216500885943 / 1000000) : ℝ) ≤ Real.exp (3 * (6473393 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6473393 / 1000000)) (270216500885943 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((723 / 2000) : ℝ) (29 / 80),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6473393 / 1000000) (40541 / 6250) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (723 / 2000) (29 / 80) (515151441 / 250000000) (20647311 / 10000000) (6473393 / 1000000) (40541 / 6250) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (723 / 2000) (29 / 80) (6473393 / 1000000) (40541 / 6250) (128699 / 1000) (64731 / 500)
    (1004967 / 1000) (511777 / 500) (2321689 / 500) (13 / 25000) (28325511 / 1000) (237 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6473393 / 1000000) (270216500885943 / 1000000) (237 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6473393 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6473393 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell189 :
    ∀ t ∈ Set.Icc ((29 / 80) : ℝ) (727 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2064731099 / 1000000000) : ℝ) ≤ Real.exp (2 * (29 / 80)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (29 / 80)) (2064731099 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((727 / 2000) : ℝ)) ≤ (413772939 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (727 / 2000)) (413772939 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((28088568722149 / 100000) : ℝ) ≤ Real.exp (3 * (405397 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (405397 / 62500)) (28088568722149 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((29 / 80) : ℝ) (727 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (405397 / 62500) (3249773 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (29 / 80) (727 / 2000) (2064731099 / 1000000000) (413772939 / 200000000) (405397 / 62500) (3249773 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (29 / 80) (727 / 2000) (405397 / 62500) (3249773 / 500000) (129293 / 1000) (130059 / 1000)
    (506581 / 500) (20637 / 20) (23577 / 5) (503 / 1000000) (14276511 / 500) (57 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (405397 / 62500) (28088568722149 / 100000) (57 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (405397 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (405397 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell190 :
    ∀ t ∈ Set.Icc ((727 / 2000) : ℝ) (729 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1034432347 / 500000000) : ℝ) ≤ Real.exp (2 * (727 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (727 / 2000)) (1034432347 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((729 / 2000) : ℝ)) ≤ (414601313 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (729 / 2000)) (414601313 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((291998641710293 / 1000000) : ℝ) ≤ Real.exp (3 * (3249669 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3249669 / 500000)) (291998641710293 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((727 / 2000) : ℝ) (729 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3249669 / 500000) (3256279 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (727 / 2000) (729 / 2000) (1034432347 / 500000000) (414601313 / 200000000) (3249669 / 500000) (3256279 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (727 / 2000) (729 / 2000) (3249669 / 500000) (3256279 / 500000) (12989 / 100) (65329 / 500)
    (127677 / 125) (208041 / 200) (957649 / 200) (487 / 1000000) (719559 / 25) (877 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3249669 / 500000) (291998641710293 / 1000000) (877 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3249669 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3249669 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell191 :
    ∀ t ∈ Set.Icc ((729 / 2000) : ℝ) (731 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((518251641 / 250000000) : ℝ) ≤ Real.exp (2 * (729 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (729 / 2000)) (518251641 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((731 / 2000) : ℝ)) ≤ (2077156727 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (731 / 2000)) (2077156727 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((37946716891469 / 125000) : ℝ) ≤ Real.exp (3 * (130247 / 20000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (130247 / 20000)) (37946716891469 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((729 / 2000) : ℝ) (731 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (130247 / 20000) (1631399 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (729 / 2000) (731 / 2000) (518251641 / 250000000) (2077156727 / 1000000000) (130247 / 20000) (1631399 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (729 / 2000) (731 / 2000) (130247 / 20000) (1631399 / 250000) (130489 / 1000) (6563 / 50)
    (1029729 / 1000) (52431 / 50) (972387 / 200) (471 / 1000000) (1450677 / 50) (211 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (130247 / 20000) (37946716891469 / 125000) (211 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (130247 / 20000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (130247 / 20000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell192 :
    ∀ t ∈ Set.Icc ((731 / 2000) : ℝ) (733 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1038578363 / 500000000) : ℝ) ≤ Real.exp (2 * (731 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (731 / 2000)) (1038578363 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((733 / 2000) : ℝ)) ≤ (2081315197 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (733 / 2000)) (2081315197 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((78907515883401 / 250000) : ℝ) ≤ Real.exp (3 * (6525387 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6525387 / 1000000)) (78907515883401 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((731 / 2000) : ℝ) (733 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6525387 / 1000000) (326933 / 50000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (731 / 2000) (733 / 2000) (1038578363 / 500000000) (2081315197 / 1000000000) (6525387 / 1000000) (326933 / 50000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (731 / 2000) (733 / 2000) (6525387 / 1000000) (326933 / 50000) (13109 / 100) (16483 / 125)
    (1038101 / 1000) (211419 / 200) (1234123 / 250) (57 / 125000) (1169863 / 40) (203 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6525387 / 1000000) (78907515883401 / 250000) (203 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6525387 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6525387 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell193 :
    ∀ t ∈ Set.Icc ((733 / 2000) : ℝ) (147 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((520328799 / 250000000) : ℝ) ≤ Real.exp (2 * (733 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (733 / 2000)) (520328799 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((147 / 400) : ℝ)) ≤ (2085481993 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (147 / 400)) (2085481993 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((82047603641793 / 250000) : ℝ) ≤ Real.exp (3 * (6538451 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6538451 / 1000000)) (82047603641793 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((733 / 2000) : ℝ) (147 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6538451 / 1000000) (6551751 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (733 / 2000) (147 / 400) (520328799 / 250000000) (2085481993 / 1000000000) (6538451 / 1000000) (6551751 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (733 / 2000) (147 / 400) (6538451 / 1000000) (6551751 / 1000000) (65847 / 500) (16559 / 125)
    (1046533 / 1000) (1065631 / 1000) (5011917 / 1000) (221 / 500000) (3685187 / 125) (781 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6538451 / 1000000) (82047603641793 / 250000) (781 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6538451 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6538451 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell194 :
    ∀ t ∈ Set.Icc ((147 / 400) : ℝ) (737 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((260685249 / 125000000) : ℝ) ≤ Real.exp (2 * (147 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (147 / 400)) (260685249 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((737 / 2000) : ℝ)) ≤ (2089657131 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (737 / 2000)) (2089657131 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((170637881382999 / 500000) : ℝ) ≤ Real.exp (3 * (6551541 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6551541 / 1000000)) (170637881382999 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((147 / 400) : ℝ) (737 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6551541 / 1000000) (6564867 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (147 / 400) (737 / 2000) (260685249 / 125000000) (2089657131 / 1000000000) (6551541 / 1000000) (6564867 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (147 / 400) (737 / 2000) (6551541 / 1000000) (6564867 / 1000000) (132301 / 1000) (133081 / 1000)
    (527513 / 500) (1074227 / 1000) (5088191 / 1000) (427 / 1000000) (29718283 / 1000) (751 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6551541 / 1000000) (170637881382999 / 500000) (751 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6551541 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6551541 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell195 :
    ∀ t ∈ Set.Icc ((737 / 2000) : ℝ) (739 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((208965713 / 100000000) : ℝ) ≤ Real.exp (2 * (737 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (737 / 2000)) (208965713 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((739 / 2000) : ℝ)) ≤ (2093840627 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (739 / 2000)) (2093840627 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((88727243865339 / 250000) : ℝ) ≤ Real.exp (3 * (6564657 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6564657 / 1000000)) (88727243865339 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((737 / 2000) : ℝ) (739 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6564657 / 1000000) (657801 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (737 / 2000) (739 / 2000) (208965713 / 100000000) (2093840627 / 1000000000) (6564657 / 1000000) (657801 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (737 / 2000) (739 / 2000) (6564657 / 1000000) (657801 / 100000) (13291 / 100) (133693 / 1000)
    (1063579 / 1000) (270721 / 250) (1033073 / 200) (413 / 1000000) (5991397 / 200) (361 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6564657 / 1000000) (88727243865339 / 250000) (361 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6564657 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6564657 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell196 :
    ∀ t ∈ Set.Icc ((739 / 2000) : ℝ) (741 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1046920313 / 500000000) : ℝ) ≤ Real.exp (2 * (739 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (739 / 2000)) (1046920313 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((741 / 2000) : ℝ)) ≤ (2098032499 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (741 / 2000)) (2098032499 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((369115053810631 / 1000000) : ℝ) ≤ Real.exp (3 * (32889 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (32889 / 5000)) (369115053810631 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((739 / 2000) : ℝ) (741 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (32889 / 5000) (6591179 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (739 / 2000) (741 / 2000) (1046920313 / 500000000) (2098032499 / 1000000000) (32889 / 5000) (6591179 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (739 / 2000) (741 / 2000) (32889 / 5000) (6591179 / 1000000) (66761 / 500) (33577 / 250)
    (536097 / 500) (1091603 / 1000) (5243411 / 1000) (1 / 2500) (30197599 / 1000) (347 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (32889 / 5000) (369115053810631 / 1000000) (347 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (32889 / 5000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (32889 / 5000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell197 :
    ∀ t ∈ Set.Icc ((741 / 2000) : ℝ) (743 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1049016249 / 500000000) : ℝ) ≤ Real.exp (2 * (741 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (741 / 2000)) (1049016249 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((743 / 2000) : ℝ)) ≤ (2102232763 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (743 / 2000)) (2102232763 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((383917962388943 / 1000000) : ℝ) ≤ Real.exp (3 * (6590969 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6590969 / 1000000)) (383917962388943 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((741 / 2000) : ℝ) (743 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6590969 / 1000000) (10567 / 1600) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (741 / 2000) (743 / 2000) (1049016249 / 500000000) (2102232763 / 1000000000) (6590969 / 1000000) (10567 / 1600) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (741 / 2000) (743 / 2000) (6590969 / 1000000) (10567 / 1600) (134137 / 1000) (67463 / 500)
    (1080871 / 1000) (220077 / 200) (2661187 / 500) (193 / 500000) (30440157 / 1000) (667 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (6590969 / 1000000) (383917962388943 / 1000000) (667 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6590969 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (6590969 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell198 :
    ∀ t ∈ Set.Icc ((743 / 2000) : ℝ) (149 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1051116381 / 500000000) : ℝ) ≤ Real.exp (2 * (743 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (743 / 2000)) (1051116381 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((149 / 400) : ℝ)) ≤ (421288287 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (149 / 400)) (421288287 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((24958988450241 / 62500) : ℝ) ≤ Real.exp (3 * (1651041 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1651041 / 250000)) (24958988450241 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((743 / 2000) : ℝ) (149 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1651041 / 250000) (6617597 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (743 / 2000) (149 / 400) (1051116381 / 500000000) (421288287 / 200000000) (1651041 / 250000) (6617597 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (743 / 2000) (149 / 400) (1651041 / 250000) (6617597 / 1000000) (67377 / 500) (67773 / 500)
    (136201 / 125) (1109229 / 1000) (5402241 / 1000) (187 / 500000) (3835582 / 125) (321 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1651041 / 250000) (24958988450241 / 62500) (321 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1651041 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1651041 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell199 :
    ∀ t ∈ Set.Icc ((149 / 400) : ℝ) (747 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1053220717 / 500000000) : ℝ) ≤ Real.exp (2 * (149 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (149 / 400)) (1053220717 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((747 / 2000) : ℝ)) ≤ (1055329267 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (747 / 2000)) (1055329267 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((51927488638039 / 125000) : ℝ) ≤ Real.exp (3 * (1323477 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1323477 / 200000)) (51927488638039 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((149 / 400) : ℝ) (747 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1323477 / 200000) (1326169 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (149 / 400) (747 / 2000) (1053220717 / 500000000) (1055329267 / 500000000) (1323477 / 200000) (1326169 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (149 / 400) (747 / 2000) (1323477 / 200000) (1326169 / 200000) (67687 / 500) (136169 / 1000)
    (137301 / 125) (223627 / 200) (2741511 / 500) (181 / 500000) (30931109 / 1000) (617 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1323477 / 200000) (51927488638039 / 125000) (617 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1323477 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1323477 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityUpperExpCompact_cellsBatch009 :
    ∀ t ∈ Set.Icc ((707 / 2000) : ℝ) (747 / 2000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell180
      hpThetaDensityUpperExpCompact_cell181)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell182
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell183
      hpThetaDensityUpperExpCompact_cell184)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell185
      hpThetaDensityUpperExpCompact_cell186)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell187
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell188
      hpThetaDensityUpperExpCompact_cell189))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell190
      hpThetaDensityUpperExpCompact_cell191)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell192
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell193
      hpThetaDensityUpperExpCompact_cell194)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell195
      hpThetaDensityUpperExpCompact_cell196)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell197
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell198
      hpThetaDensityUpperExpCompact_cell199)))))

#print axioms hpThetaDensityUpperExpCompact_cellsBatch009
end HodgeProofHP
