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
theorem hpThetaDensityUpperExpCompact_cell280 :
    ∀ t ∈ Set.Icc ((907 / 2000) : ℝ) (909 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2476880733 / 1000000000) : ℝ) ≤ Real.exp (2 * (907 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (907 / 2000)) (2476880733 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((909 / 2000) : ℝ)) ≤ (2481839453 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (909 / 2000)) (2481839453 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((13035822830408343 / 1000000) : ℝ) ≤ Real.exp (3 * (24316 / 3125)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (24316 / 3125)) (13035822830408343 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((907 / 2000) : ℝ) (909 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (24316 / 3125) (7796947 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (907 / 2000) (909 / 2000) (2476880733 / 1000000000) (2481839453 / 1000000000) (24316 / 3125) (7796947 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (907 / 2000) (909 / 2000) (24316 / 3125) (7796947 / 1000000) (195401 / 1000) (196483 / 1000)
    (103093 / 50) (104627 / 50) (4026391 / 250) (1 / 50000) (59131421 / 1000) (1 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (24316 / 3125) (13035822830408343 / 1000000) (1 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (24316 / 3125)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (24316 / 3125)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell281 :
    ∀ t ∈ Set.Icc ((909 / 2000) : ℝ) (911 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2481839451 / 1000000000) : ℝ) ≤ Real.exp (2 * (909 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (909 / 2000)) (2481839451 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((911 / 2000) : ℝ)) ≤ (2486808099 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (911 / 2000)) (2486808099 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((13643964460043663 / 1000000) : ℝ) ≤ Real.exp (3 * (3898349 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3898349 / 500000)) (13643964460043663 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((909 / 2000) : ℝ) (911 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3898349 / 500000) (7812557 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (909 / 2000) (911 / 2000) (2481839451 / 1000000000) (2486808099 / 1000000000) (3898349 / 500000) (7812557 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (909 / 2000) (911 / 2000) (3898349 / 500000) (7812557 / 1000000) (98139 / 500) (49341 / 250)
    (415493 / 200) (421663 / 200) (4075651 / 250) (19 / 1000000) (11921277 / 200) (19 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3898349 / 500000) (13643964460043663 / 1000000) (19 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3898349 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3898349 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell282 :
    ∀ t ∈ Set.Icc ((911 / 2000) : ℝ) (913 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2486808097 / 1000000000) : ℝ) ≤ Real.exp (2 * (911 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (911 / 2000)) (2486808097 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((913 / 2000) : ℝ)) ≤ (622946673 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (913 / 2000)) (622946673 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((14281503932919319 / 1000000) : ℝ) ≤ Real.exp (3 * (7812307 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (7812307 / 1000000)) (14281503932919319 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((911 / 2000) : ℝ) (913 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (7812307 / 1000000) (3914099 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (911 / 2000) (913 / 2000) (2486808097 / 1000000000) (622946673 / 250000000) (7812307 / 1000000) (3914099 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (911 / 2000) (913 / 2000) (7812307 / 1000000) (3914099 / 500000) (197159 / 1000) (198249 / 1000)
    (1046589 / 500) (1062099 / 500) (2062713 / 125) (9 / 500000) (15021289 / 250) (9 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (7812307 / 1000000) (14281503932919319 / 1000000) (9 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7812307 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7812307 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell283 :
    ∀ t ∈ Set.Icc ((913 / 2000) : ℝ) (183 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((249178669 / 100000000) : ℝ) ≤ Real.exp (2 * (913 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (913 / 2000)) (249178669 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((183 / 400) : ℝ)) ≤ (624193813 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (183 / 400)) (624193813 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((3737476069839337 / 250000) : ℝ) ≤ Real.exp (3 * (7827947 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (7827947 / 1000000)) (3737476069839337 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((913 / 2000) : ℝ) (183 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (7827947 / 1000000) (784387 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (913 / 2000) (183 / 400) (249178669 / 100000000) (624193813 / 250000000) (7827947 / 1000000) (784387 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (913 / 2000) (183 / 400) (7827947 / 1000000) (784387 / 100000) (198043 / 1000) (99569 / 500)
    (2108999 / 1000) (214019 / 100) (16702881 / 1000) (9 / 500000) (60567763 / 1000) (9 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (7827947 / 1000000) (3737476069839337 / 250000) (9 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7827947 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7827947 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell284 :
    ∀ t ∈ Set.Icc ((183 / 400) : ℝ) (917 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2496775251 / 1000000000) : ℝ) ≤ Real.exp (2 * (183 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (183 / 400)) (2496775251 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((917 / 2000) : ℝ)) ≤ (12508869 / 5000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (917 / 2000)) (12508869 / 5000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((626029953486401 / 40000) : ℝ) ≤ Real.exp (3 * (7843619 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (7843619 / 1000000)) (626029953486401 / 40000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((183 / 400) : ℝ) (917 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (7843619 / 1000000) (7859573 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (183 / 400) (917 / 2000) (2496775251 / 1000000000) (12508869 / 5000000) (7843619 / 1000000) (7859573 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (183 / 400) (917 / 2000) (7843619 / 1000000) (7859573 / 1000000) (198931 / 1000) (20003 / 100)
    (2124931 / 1000) (2156291 / 1000) (2113267 / 125) (17 / 1000000) (12210847 / 200) (17 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (7843619 / 1000000) (626029953486401 / 40000) (17 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7843619 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7843619 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell285 :
    ∀ t ∈ Set.Icc ((917 / 2000) : ℝ) (919 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1250886899 / 500000000) : ℝ) ≤ Real.exp (2 * (917 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (917 / 2000)) (1250886899 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((919 / 2000) : ℝ)) ≤ (1253391177 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (919 / 2000)) (1253391177 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((16385612154834019 / 1000000) : ℝ) ≤ Real.exp (3 * (3929661 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3929661 / 500000)) (16385612154834019 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((917 / 2000) : ℝ) (919 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3929661 / 500000) (1968827 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (917 / 2000) (919 / 2000) (1250886899 / 500000000) (1253391177 / 500000000) (3929661 / 500000) (1968827 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (917 / 2000) (919 / 2000) (3929661 / 500000) (1968827 / 250000) (199823 / 1000) (100463 / 500)
    (2140971 / 1000) (434501 / 200) (17111541 / 1000) (1 / 62500) (7693079 / 125) (1 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3929661 / 500000) (16385612154834019 / 1000000) (1 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3929661 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3929661 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell286 :
    ∀ t ∈ Set.Icc ((919 / 2000) : ℝ) (921 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((156673897 / 62500000) : ℝ) ≤ Real.exp (2 * (919 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (919 / 2000)) (156673897 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((921 / 2000) : ℝ)) ≤ (313975117 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (921 / 2000)) (313975117 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1715619309496343 / 100000) : ℝ) ≤ Real.exp (3 * (492191 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (492191 / 62500)) (1715619309496343 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((919 / 2000) : ℝ) (921 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (492191 / 62500) (3945537 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (919 / 2000) (921 / 2000) (156673897 / 62500000) (313975117 / 125000000) (492191 / 62500) (3945537 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (919 / 2000) (921 / 2000) (492191 / 62500) (3945537 / 500000) (200719 / 1000) (100913 / 500)
    (1078561 / 500) (2188829 / 1000) (8659541 / 500) (3 / 200000) (7754869 / 125) (3 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (492191 / 62500) (1715619309496343 / 100000) (3 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (492191 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (492191 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell287 :
    ∀ t ∈ Set.Icc ((921 / 2000) : ℝ) (923 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1255900467 / 500000000) : ℝ) ≤ Real.exp (2 * (921 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (921 / 2000)) (1255900467 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((923 / 2000) : ℝ)) ≤ (503365913 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (923 / 2000)) (503365913 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8982164895083411 / 500000) : ℝ) ≤ Real.exp (3 * (3945411 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3945411 / 500000)) (8982164895083411 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((921 / 2000) : ℝ) (923 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3945411 / 500000) (988359 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (921 / 2000) (923 / 2000) (1255900467 / 500000000) (503365913 / 200000000) (3945411 / 500000) (988359 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (921 / 2000) (923 / 2000) (3945411 / 500000) (988359 / 125000) (201619 / 1000) (20273 / 100)
    (271673 / 125) (1102633 / 500) (2191099 / 125) (3 / 200000) (7817157 / 125) (3 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3945411 / 500000) (8982164895083411 / 500000) (3 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3945411 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3945411 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell288 :
    ∀ t ∈ Set.Icc ((923 / 2000) : ℝ) (37 / 80), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2516829563 / 1000000000) : ℝ) ≤ Real.exp (2 * (923 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (923 / 2000)) (2516829563 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((37 / 80) : ℝ)) ≤ (2521868261 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (37 / 80)) (2521868261 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1881190664361321 / 100000) : ℝ) ≤ Real.exp (3 * (395331 / 50000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (395331 / 50000)) (1881190664361321 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((923 / 2000) : ℝ) (37 / 80),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (395331 / 50000) (3961351 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (923 / 2000) (37 / 80) (2516829563 / 1000000000) (2521868261 / 1000000000) (395331 / 50000) (3961351 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (923 / 2000) (37 / 80) (395331 / 50000) (3961351 / 500000) (101261 / 500) (101819 / 500)
    (2189759 / 1000) (277727 / 125) (17740691 / 1000) (7 / 500000) (31519787 / 500) (7 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (395331 / 50000) (1881190664361321 / 100000) (7 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (395331 / 50000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (395331 / 50000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell289 :
    ∀ t ∈ Set.Icc ((37 / 80) : ℝ) (927 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2521868259 / 1000000000) : ℝ) ≤ Real.exp (2 * (37 / 80)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (37 / 80)) (2521868259 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((927 / 2000) : ℝ)) ≤ (631729261 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (927 / 2000)) (631729261 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((9850423717616293 / 500000) : ℝ) ≤ Real.exp (3 * (7922449 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (7922449 / 1000000)) (9850423717616293 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((37 / 80) : ℝ) (927 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (7922449 / 1000000) (7938563 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (37 / 80) (927 / 2000) (2521868259 / 1000000000) (631729261 / 250000000) (7922449 / 1000000) (7938563 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (37 / 80) (927 / 2000) (7922449 / 1000000) (7938563 / 1000000) (203429 / 1000) (204549 / 1000)
    (441249 / 200) (2238479 / 1000) (3590957 / 200) (7 / 500000) (12709181 / 200) (13 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (7922449 / 1000000) (9850423717616293 / 500000) (13 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7922449 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7922449 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell290 :
    ∀ t ∈ Set.Icc ((927 / 2000) : ℝ) (929 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2526917043 / 1000000000) : ℝ) ≤ Real.exp (2 * (927 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (927 / 2000)) (2526917043 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((929 / 2000) : ℝ)) ≤ (9890531 / 3906250) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (929 / 2000)) (9890531 / 3906250) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2063322722432907 / 100000) : ℝ) ≤ Real.exp (3 * (7938309 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (7938309 / 1000000)) (2063322722432907 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((927 / 2000) : ℝ) (929 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (7938309 / 1000000) (994307 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (927 / 2000) (929 / 2000) (2526917043 / 1000000000) (9890531 / 3906250) (7938309 / 1000000) (994307 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (927 / 2000) (929 / 2000) (7938309 / 1000000) (994307 / 125000) (10217 / 50) (25683 / 125)
    (555711 / 250) (2255257 / 1000) (1817113 / 100) (7 / 500000) (64056311 / 1000) (13 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (7938309 / 1000000) (2063322722432907 / 100000) (13 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7938309 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7938309 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell291 :
    ∀ t ∈ Set.Icc ((929 / 2000) : ℝ) (931 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1265987967 / 500000000) : ℝ) ≤ Real.exp (2 * (929 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (929 / 2000)) (1265987967 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((931 / 2000) : ℝ)) ≤ (507408991 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (931 / 2000)) (507408991 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((21611353465745947 / 1000000) : ℝ) ≤ Real.exp (3 * (3977101 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3977101 / 500000)) (21611353465745947 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((929 / 2000) : ℝ) (931 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3977101 / 500000) (7970381 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (929 / 2000) (931 / 2000) (1265987967 / 500000000) (507408991 / 200000000) (3977101 / 500000) (7970381 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (929 / 2000) (931 / 2000) (3977101 / 500000) (7970381 / 1000000) (41051 / 200) (206383 / 1000)
    (55989 / 25) (45443 / 20) (18389703 / 1000) (13 / 1000000) (32285411 / 500) (3 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3977101 / 500000) (21611353465745947 / 1000000) (3 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3977101 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3977101 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell292 :
    ∀ t ∈ Set.Icc ((931 / 2000) : ℝ) (933 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2537044953 / 1000000000) : ℝ) ≤ Real.exp (2 * (931 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (931 / 2000)) (2537044953 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((933 / 2000) : ℝ)) ≤ (1271062061 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (933 / 2000)) (1271062061 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((11318702805267091 / 500000) : ℝ) ≤ Real.exp (3 * (3985063 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3985063 / 500000)) (11318702805267091 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((931 / 2000) : ℝ) (933 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3985063 / 500000) (3993169 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (931 / 2000) (933 / 2000) (2537044953 / 1000000000) (1271062061 / 500000000) (3985063 / 500000) (3993169 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (931 / 2000) (933 / 2000) (3985063 / 500000) (3993169 / 500000) (206173 / 1000) (103653 / 500)
    (564097 / 250) (2289159 / 1000) (2326321 / 125) (13 / 1000000) (6508947 / 100) (3 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3985063 / 500000) (11318702805267091 / 500000) (3 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3985063 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3985063 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell293 :
    ∀ t ∈ Set.Icc ((933 / 2000) : ℝ) (187 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((63553103 / 25000000) : ℝ) ≤ Real.exp (2 * (933 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (933 / 2000)) (63553103 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((187 / 400) : ℝ)) ≤ (1273606729 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (187 / 400)) (1273606729 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((23713864978626981 / 1000000) : ℝ) ≤ Real.exp (3 * (3993041 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3993041 / 500000)) (23713864978626981 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((933 / 2000) : ℝ) (187 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3993041 / 500000) (4001163 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (933 / 2000) (187 / 400) (63553103 / 25000000) (1273606729 / 500000000) (3993041 / 500000) (4001163 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (933 / 2000) (187 / 400) (3993041 / 500000) (4001163 / 500000) (25887 / 125) (208233 / 1000)
    (2273333 / 1000) (576571 / 250) (2354211 / 125) (3 / 250000) (16403063 / 250) (11 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3993041 / 500000) (23713864978626981 / 1000000) (11 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3993041 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3993041 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell294 :
    ∀ t ∈ Set.Icc ((187 / 400) : ℝ) (937 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((159200841 / 62500000) : ℝ) ≤ Real.exp (2 * (187 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (187 / 400)) (159200841 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((937 / 2000) : ℝ)) ≤ (2552312983 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (937 / 2000)) (2552312983 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((24843350010348079 / 1000000) : ℝ) ≤ Real.exp (3 * (8002071 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (8002071 / 1000000)) (24843350010348079 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((187 / 400) : ℝ) (937 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (8002071 / 1000000) (8018347 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (187 / 400) (937 / 2000) (159200841 / 62500000) (2552312983 / 1000000000) (8002071 / 1000000) (8018347 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (187 / 400) (937 / 2000) (8002071 / 1000000) (8018347 / 1000000) (104011 / 500) (52291 / 250)
    (572599 / 250) (2323527 / 1000) (9529567 / 500) (3 / 250000) (33069633 / 500) (11 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (8002071 / 1000000) (24843350010348079 / 1000000) (11 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8002071 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8002071 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell295 :
    ∀ t ∈ Set.Icc ((937 / 2000) : ℝ) (939 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2552312981 / 1000000000) : ℝ) ≤ Real.exp (2 * (937 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (937 / 2000)) (2552312981 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((939 / 2000) : ℝ)) ≤ (2557422717 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (939 / 2000)) (2557422717 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1626774829586257 / 62500) : ℝ) ≤ Real.exp (3 * (8018091 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (8018091 / 1000000)) (1626774829586257 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((937 / 2000) : ℝ) (939 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (8018091 / 1000000) (10043 / 1250) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (937 / 2000) (939 / 2000) (2552312981 / 1000000000) (2557422717 / 1000000000) (8018091 / 1000000) (10043 / 1250) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (937 / 2000) (939 / 2000) (8018091 / 1000000) (10043 / 1250) (26119 / 125) (105049 / 500)
    (1153787 / 500) (2340889 / 1000) (3857387 / 200) (11 / 1000000) (66670511 / 1000) (1 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (8018091 / 1000000) (1626774829586257 / 62500) (1 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8018091 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8018091 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell296 :
    ∀ t ∈ Set.Icc ((939 / 2000) : ℝ) (941 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((511484543 / 200000000) : ℝ) ≤ Real.exp (2 * (939 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (939 / 2000)) (511484543 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((941 / 2000) : ℝ)) ≤ (2562542681 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (941 / 2000)) (2562542681 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((27271891999550589 / 1000000) : ℝ) ≤ Real.exp (3 * (8034143 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (8034143 / 1000000)) (27271891999550589 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((939 / 2000) : ℝ) (941 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (8034143 / 1000000) (1610097 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (939 / 2000) (941 / 2000) (511484543 / 200000000) (2562542681 / 1000000000) (8034143 / 1000000) (1610097 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (939 / 2000) (941 / 2000) (8034143 / 1000000) (1610097 / 200000) (104943 / 500) (211037 / 1000)
    (232487 / 100) (235837 / 100) (1951709 / 100) (11 / 1000000) (33603009 / 500) (1 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (8034143 / 1000000) (27271891999550589 / 1000000) (1 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8034143 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8034143 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell297 :
    ∀ t ∈ Set.Icc ((941 / 2000) : ℝ) (943 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2562542679 / 1000000000) : ℝ) ≤ Real.exp (2 * (941 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (941 / 2000)) (2562542679 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((943 / 2000) : ℝ)) ≤ (513534579 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (943 / 2000)) (513534579 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((14288398083303109 / 500000) : ℝ) ≤ Real.exp (3 * (8050227 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (8050227 / 1000000)) (14288398083303109 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((941 / 2000) : ℝ) (943 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (8050227 / 1000000) (4033301 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (941 / 2000) (943 / 2000) (2562542679 / 1000000000) (513534579 / 200000000) (8050227 / 1000000) (4033301 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (941 / 2000) (943 / 2000) (8050227 / 1000000) (4033301 / 500000) (8433 / 40) (211979 / 1000)
    (468457 / 200) (237597 / 100) (19749621 / 1000) (1 / 100000) (3387291 / 50) (9 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (8050227 / 1000000) (14288398083303109 / 500000) (9 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8050227 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8050227 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell298 :
    ∀ t ∈ Set.Icc ((943 / 2000) : ℝ) (189 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((641918223 / 250000000) : ℝ) ≤ Real.exp (2 * (943 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (943 / 2000)) (641918223 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((189 / 400) : ℝ)) ≤ (2572813379 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (189 / 400)) (2572813379 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((29946312163825977 / 1000000) : ℝ) ≤ Real.exp (3 * (1008293 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1008293 / 125000)) (29946312163825977 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((943 / 2000) : ℝ) (189 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1008293 / 125000) (8082751 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (943 / 2000) (189 / 400) (641918223 / 250000000) (2572813379 / 1000000000) (1008293 / 125000) (8082751 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (943 / 2000) (189 / 400) (1008293 / 125000) (8082751 / 1000000) (211767 / 1000) (106463 / 500)
    (2359821 / 1000) (2393689 / 1000) (2498066 / 125) (1 / 100000) (68289949 / 1000) (9 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1008293 / 125000) (29946312163825977 / 1000000) (9 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1008293 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1008293 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityUpperExpCompact_cell299 :
    ∀ t ∈ Set.Icc ((189 / 400) : ℝ) (947 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2572813377 / 1000000000) : ℝ) ≤ Real.exp (2 * (189 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (189 / 400)) (2572813377 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((947 / 2000) : ℝ)) ≤ (515592831 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (947 / 2000)) (515592831 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((15691819136299563 / 500000) : ℝ) ≤ Real.exp (3 * (8082493 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (8082493 / 1000000)) (15691819136299563 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((189 / 400) : ℝ) (947 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (8082493 / 1000000) (8098933 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (189 / 400) (947 / 2000) (2572813377 / 1000000000) (515592831 / 200000000) (8082493 / 1000000) (8098933 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (189 / 400) (947 / 2000) (8082493 / 1000000) (8098933 / 1000000) (212713 / 1000) (53469 / 250)
    (594369 / 250) (602883 / 250) (2022189 / 100) (1 / 100000) (6883847 / 100) (9 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (8082493 / 1000000) (15691819136299563 / 500000) (9 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8082493 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (8082493 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityUpperExpCompact_cellsBatch014 :
    ∀ t ∈ Set.Icc ((907 / 2000) : ℝ) (947 / 2000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell280
      hpThetaDensityUpperExpCompact_cell281)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell282
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell283
      hpThetaDensityUpperExpCompact_cell284)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell285
      hpThetaDensityUpperExpCompact_cell286)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell287
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell288
      hpThetaDensityUpperExpCompact_cell289))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell290
      hpThetaDensityUpperExpCompact_cell291)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell292
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell293
      hpThetaDensityUpperExpCompact_cell294)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell295
      hpThetaDensityUpperExpCompact_cell296)
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell297
      (hpThetaDensityCells_positive_glue hpThetaDensityUpperExpCompact_cell298
      hpThetaDensityUpperExpCompact_cell299)))))

#print axioms hpThetaDensityUpperExpCompact_cellsBatch014
end HodgeProofHP
