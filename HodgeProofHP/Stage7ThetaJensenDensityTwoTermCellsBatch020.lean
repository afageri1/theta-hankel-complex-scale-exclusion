/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0400 :
    ∀ t ∈ Set.Icc ((1649 / 64000) : ℝ) (33 / 1280), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1052882088343 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1649 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1649 / 64000)) (1052882088343 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((33 / 1280) : ℝ)) ≤ (1052914991423 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (33 / 1280)) (1052914991423 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((232412161 / 125000000) : ℝ) ≤ Real.exp (3 * (661545189 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (661545189 / 200000000) / 16) (232412161 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3307830367 / 1000000000) : ℝ) / 16) ≤ (1859333693 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3307830367 / 1000000000) / 16) (1859333693 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1649 / 64000) : ℝ) (33 / 1280),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (661545189 / 200000000) (3307830367 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1649 / 64000) (33 / 1280) (1052882088343 / 1000000000000) (1052914991423 / 1000000000000) (661545189 / 200000000) (3307830367 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1649 / 64000) (33 / 1280) (661545189 / 200000000) (3307830367 / 1000000000) (49009759 / 1000000000000) (12256279 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (661545189 / 200000000) (3307830367 / 1000000000) (232412161 / 125000000) (1859333693 / 1000000000) (49009759 / 1000000000000) (12256279 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0401 :
    ∀ t ∈ Set.Icc ((33 / 1280) : ℝ) (1651 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((526457495711 / 500000000000) : ℝ) ≤ Real.exp (2 * (33 / 1280)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (33 / 1280)) (526457495711 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1651 / 64000) : ℝ)) ≤ (1052947895531 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1651 / 64000)) (1052947895531 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((74373333 / 40000000) : ℝ) ≤ Real.exp (3 * (3307829313 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3307829313 / 1000000000) / 16) (74373333 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1653966869 / 500000000) : ℝ) / 16) ≤ (1859369731 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1653966869 / 500000000) / 16) (1859369731 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((33 / 1280) : ℝ) (1651 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3307829313 / 1000000000) (1653966869 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (33 / 1280) (1651 / 64000) (526457495711 / 500000000000) (1052947895531 / 1000000000000) (3307829313 / 1000000000) (1653966869 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (33 / 1280) (1651 / 64000) (3307829313 / 1000000000) (1653966869 / 500000000) (48994563 / 1000000000000) (9801983 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3307829313 / 1000000000) (1653966869 / 500000000) (74373333 / 40000000) (1859369731 / 1000000000) (48994563 / 1000000000000) (9801983 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0402 :
    ∀ t ∈ Set.Icc ((1651 / 64000) : ℝ) (413 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((105294789553 / 100000000000) : ℝ) ≤ Real.exp (2 * (1651 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1651 / 64000)) (105294789553 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((413 / 16000) : ℝ)) ≤ (1052980800667 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (413 / 16000)) (1052980800667 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1859369363 / 1000000000) : ℝ) ≤ Real.exp (3 * (661586537 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (661586537 / 200000000) / 16) (1859369363 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3308037113 / 1000000000) : ℝ) / 16) ≤ (1859405771 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3308037113 / 1000000000) / 16) (1859405771 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1651 / 64000) : ℝ) (413 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (661586537 / 200000000) (3308037113 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1651 / 64000) (413 / 16000) (105294789553 / 100000000000) (1052980800667 / 1000000000000) (661586537 / 200000000) (3308037113 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1651 / 64000) (413 / 16000) (661586537 / 200000000) (3308037113 / 1000000000) (48979371 / 1000000000000) (48994719 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (661586537 / 200000000) (3308037113 / 1000000000) (1859369363 / 1000000000) (1859405771 / 1000000000) (48979371 / 1000000000000) (48994719 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0403 :
    ∀ t ∈ Set.Icc ((413 / 16000) : ℝ) (1653 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((526490400333 / 500000000000) : ℝ) ≤ Real.exp (2 * (413 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (413 / 16000)) (526490400333 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1653 / 64000) : ℝ)) ≤ (1053013706831 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1653 / 64000)) (1053013706831 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1859405403 / 1000000000) : ℝ) ≤ Real.exp (3 * (3308036059 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3308036059 / 1000000000) / 16) (1859405403 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3308140491 / 1000000000) : ℝ) / 16) ≤ (1859441813 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3308140491 / 1000000000) / 16) (1859441813 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((413 / 16000) : ℝ) (1653 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3308036059 / 1000000000) (3308140491 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (413 / 16000) (1653 / 64000) (526490400333 / 500000000000) (1053013706831 / 1000000000000) (3308036059 / 1000000000) (3308140491 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (413 / 16000) (1653 / 64000) (3308036059 / 1000000000) (3308140491 / 1000000000) (48964183 / 1000000000000) (48979527 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3308036059 / 1000000000) (3308140491 / 1000000000) (1859405403 / 1000000000) (1859441813 / 1000000000) (48964183 / 1000000000000) (48979527 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0404 :
    ∀ t ∈ Set.Icc ((1653 / 64000) : ℝ) (331 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((105301370683 / 100000000000) : ℝ) ≤ Real.exp (2 * (1653 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1653 / 64000)) (105301370683 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((331 / 12800) : ℝ)) ≤ (263269880561 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (331 / 12800)) (263269880561 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((371888289 / 200000000) : ℝ) ≤ Real.exp (3 * (3308139437 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3308139437 / 1000000000) / 16) (371888289 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((413543407 / 125000000) : ℝ) / 16) ≤ (929756951 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (413543407 / 125000000) / 16) (929756951 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1653 / 64000) : ℝ) (331 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3308139437 / 1000000000) (413543407 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1653 / 64000) (331 / 12800) (105301370683 / 100000000000) (263269880561 / 250000000000) (3308139437 / 1000000000) (413543407 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1653 / 64000) (331 / 12800) (3308139437 / 1000000000) (413543407 / 125000000) (2446691 / 50000000000) (48964339 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3308139437 / 1000000000) (413543407 / 125000000) (371888289 / 200000000) (929756951 / 500000000) (2446691 / 50000000000) (48964339 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0405 :
    ∀ t ∈ Set.Icc ((331 / 12800) : ℝ) (1657 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1053079522243 / 1000000000000) : ℝ) ≤ Real.exp (2 * (331 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (331 / 12800)) (1053079522243 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1657 / 64000) : ℝ)) ≤ (1053145341771 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1657 / 64000)) (1053145341771 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((929756767 / 500000000) : ℝ) ≤ Real.exp (3 * (1654173101 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1654173101 / 500000000) / 16) (929756767 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1654277017 / 500000000) : ℝ) / 16) ≤ (1859585999 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1654277017 / 500000000) / 16) (1859585999 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((331 / 12800) : ℝ) (1657 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1654173101 / 500000000) (1654277017 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (331 / 12800) (1657 / 64000) (1053079522243 / 1000000000000) (1053145341771 / 1000000000000) (1654173101 / 500000000) (1654277017 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (331 / 12800) (1657 / 64000) (1654173101 / 500000000) (1654277017 / 500000000) (24451737 / 500000000000) (6116747 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1654173101 / 500000000) (1654277017 / 500000000) (929756767 / 500000000) (1859585999 / 1000000000) (24451737 / 500000000000) (6116747 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0406 :
    ∀ t ∈ Set.Icc ((1657 / 64000) : ℝ) (1659 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((105314534177 / 100000000000) : ℝ) ≤ Real.exp (2 * (1657 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1657 / 64000)) (105314534177 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1659 / 64000) : ℝ)) ≤ (263302791353 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1659 / 64000)) (263302791353 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((185958563 / 100000000) : ℝ) ≤ Real.exp (3 * (165427649 / 50000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (165427649 / 50000000) / 16) (185958563 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((132350433 / 40000000) : ℝ) / 16) ≤ (929829051 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (132350433 / 40000000) / 16) (929829051 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1657 / 64000) : ℝ) (1659 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (165427649 / 50000000) (132350433 / 40000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1657 / 64000) (1659 / 64000) (105314534177 / 100000000000) (263302791353 / 250000000000) (165427649 / 50000000) (132350433 / 40000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1657 / 64000) (1659 / 64000) (165427649 / 50000000) (132350433 / 40000000) (9774629 / 200000000000) (4890363 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (165427649 / 50000000) (132350433 / 40000000) (185958563 / 100000000) (929829051 / 500000000) (9774629 / 200000000000) (4890363 / 100000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0407 :
    ∀ t ∈ Set.Icc ((1659 / 64000) : ℝ) (1661 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1053211165411 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1659 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1659 / 64000)) (1053211165411 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1661 / 64000) : ℝ)) ≤ (1053276993167 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1661 / 64000)) (1053276993167 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((929828867 / 500000000) : ℝ) ≤ Real.exp (3 * (3308759771 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3308759771 / 1000000000) / 16) (929828867 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3308967629 / 1000000000) : ℝ) / 16) ≤ (929865107 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3308967629 / 1000000000) / 16) (929865107 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1659 / 64000) : ℝ) (1661 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3308759771 / 1000000000) (3308967629 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1659 / 64000) (1661 / 64000) (1053211165411 / 1000000000000) (1053276993167 / 1000000000000) (3308759771 / 1000000000) (3308967629 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1659 / 64000) (1661 / 64000) (3308759771 / 1000000000) (3308967629 / 1000000000) (48842833 / 1000000000000) (48873301 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3308759771 / 1000000000) (3308967629 / 1000000000) (929828867 / 500000000) (929865107 / 500000000) (48842833 / 1000000000000) (48873301 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0408 :
    ∀ t ∈ Set.Icc ((1661 / 64000) : ℝ) (1663 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((526638496583 / 500000000000) : ℝ) ≤ Real.exp (2 * (1661 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1661 / 64000)) (526638496583 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1663 / 64000) : ℝ)) ≤ (263335706259 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1663 / 64000)) (263335706259 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((371945969 / 200000000) : ℝ) ≤ Real.exp (3 * (132358663 / 40000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (132358663 / 40000000) / 16) (371945969 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1654587223 / 500000000) : ℝ) / 16) ≤ (464950583 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1654587223 / 500000000) / 16) (464950583 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1661 / 64000) : ℝ) (1663 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (132358663 / 40000000) (1654587223 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1661 / 64000) (1663 / 64000) (526638496583 / 500000000000) (263335706259 / 250000000000) (132358663 / 40000000) (1654587223 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1661 / 64000) (1663 / 64000) (132358663 / 40000000) (1654587223 / 500000000) (24406269 / 500000000000) (48842989 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (132358663 / 40000000) (1654587223 / 500000000) (371945969 / 200000000) (464950583 / 250000000) (24406269 / 500000000000) (48842989 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0409 :
    ∀ t ∈ Set.Icc ((1663 / 64000) : ℝ) (333 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((210668565007 / 200000000000) : ℝ) ≤ Real.exp (2 * (1663 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1663 / 64000)) (210668565007 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((333 / 12800) : ℝ)) ≤ (52670433051 / 50000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (333 / 12800)) (52670433051 / 50000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1859801963 / 1000000000) : ℝ) ≤ Real.exp (3 * (206823337 / 62500000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (206823337 / 62500000) / 16) (1859801963 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((827345319 / 250000000) : ℝ) / 16) ≤ (929937229 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (827345319 / 250000000) / 16) (929937229 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1663 / 64000) : ℝ) (333 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (206823337 / 62500000) (827345319 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1663 / 64000) (333 / 12800) (210668565007 / 200000000000) (52670433051 / 50000000000) (206823337 / 62500000) (827345319 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1663 / 64000) (333 / 12800) (206823337 / 62500000) (827345319 / 250000000) (48782259 / 1000000000000) (24406347 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (206823337 / 62500000) (827345319 / 250000000) (1859801963 / 1000000000) (929937229 / 500000000) (48782259 / 1000000000000) (24406347 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0410 :
    ∀ t ∈ Set.Icc ((333 / 12800) : ℝ) (1667 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1053408661019 / 1000000000000) : ℝ) ≤ Real.exp (2 * (333 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (333 / 12800)) (1053408661019 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1667 / 64000) : ℝ)) ≤ (1053474501119 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1667 / 64000)) (1053474501119 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1859874089 / 1000000000) : ℝ) ≤ Real.exp (3 * (1654690111 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1654690111 / 500000000) / 16) (1859874089 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3309588119 / 1000000000) : ℝ) / 16) ≤ (1859946591 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3309588119 / 1000000000) / 16) (1859946591 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((333 / 12800) : ℝ) (1667 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1654690111 / 500000000) (3309588119 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (333 / 12800) (1667 / 64000) (1053408661019 / 1000000000000) (1053474501119 / 1000000000000) (1654690111 / 500000000) (3309588119 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (333 / 12800) (1667 / 64000) (1654690111 / 500000000) (3309588119 / 1000000000) (24375999 / 500000000000) (9756483 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1654690111 / 500000000) (3309588119 / 1000000000) (1859874089 / 1000000000) (1859946591 / 1000000000) (24375999 / 500000000000) (9756483 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0411 :
    ∀ t ∈ Set.Icc ((1667 / 64000) : ℝ) (1669 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((526737250559 / 500000000000) : ℝ) ≤ Real.exp (2 * (1667 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1667 / 64000)) (526737250559 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1669 / 64000) : ℝ)) ≤ (1053540345333 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1669 / 64000)) (1053540345333 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((929973111 / 500000000) : ℝ) ≤ Real.exp (3 * (413698383 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (413698383 / 125000000) / 16) (929973111 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((132391799 / 40000000) : ℝ) / 16) ≤ (1860018731 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (132391799 / 40000000) / 16) (1860018731 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1667 / 64000) : ℝ) (1669 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (413698383 / 125000000) (132391799 / 40000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1667 / 64000) (1669 / 64000) (526737250559 / 500000000000) (1053540345333 / 1000000000000) (413698383 / 125000000) (132391799 / 40000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1667 / 64000) (1669 / 64000) (413698383 / 125000000) (132391799 / 40000000) (24360877 / 500000000000) (24376077 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (413698383 / 125000000) (132391799 / 40000000) (929973111 / 500000000) (1860018731 / 1000000000) (24360877 / 500000000000) (24376077 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0412 :
    ∀ t ∈ Set.Icc ((1669 / 64000) : ℝ) (1671 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((263385086333 / 250000000000) : ℝ) ≤ Real.exp (2 * (1669 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1669 / 64000)) (263385086333 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1671 / 64000) : ℝ)) ≤ (526803096831 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1671 / 64000)) (526803096831 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((930009181 / 500000000) : ℝ) ≤ Real.exp (3 * (5171553 / 1562500) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5171553 / 1562500) / 16) (930009181 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3310001843 / 1000000000) : ℝ) / 16) ≤ (930045439 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3310001843 / 1000000000) / 16) (930045439 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1669 / 64000) : ℝ) (1671 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5171553 / 1562500) (3310001843 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1669 / 64000) (1671 / 64000) (263385086333 / 250000000000) (526803096831 / 500000000000) (5171553 / 1562500) (3310001843 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1669 / 64000) (1671 / 64000) (5171553 / 1562500) (3310001843 / 1000000000) (24345763 / 500000000000) (48721909 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (5171553 / 1562500) (3310001843 / 1000000000) (930009181 / 500000000) (930045439 / 500000000) (24345763 / 500000000000) (48721909 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0413 :
    ∀ t ∈ Set.Icc ((1671 / 64000) : ℝ) (1673 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1053606193661 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1671 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1671 / 64000)) (1053606193661 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1673 / 64000) : ℝ)) ≤ (1053672046107 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1673 / 64000)) (1053672046107 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((186009051 / 100000000) : ℝ) ≤ Real.exp (3 * (3310000789 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3310000789 / 1000000000) / 16) (186009051 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((132408349 / 40000000) : ℝ) / 16) ≤ (1860163033 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (132408349 / 40000000) / 16) (1860163033 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1671 / 64000) : ℝ) (1673 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3310000789 / 1000000000) (132408349 / 40000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1671 / 64000) (1673 / 64000) (1053606193661 / 1000000000000) (1053672046107 / 1000000000000) (3310000789 / 1000000000) (132408349 / 40000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1671 / 64000) (1673 / 64000) (3310000789 / 1000000000) (132408349 / 40000000) (9732263 / 200000000000) (48691681 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3310000789 / 1000000000) (132408349 / 40000000) (186009051 / 100000000) (1860163033 / 1000000000) (9732263 / 200000000000) (48691681 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0414 :
    ∀ t ∈ Set.Icc ((1673 / 64000) : ℝ) (67 / 2560), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((526836023053 / 500000000000) : ℝ) ≤ Real.exp (2 * (1673 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1673 / 64000)) (526836023053 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((67 / 2560) : ℝ)) ≤ (263434475667 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (67 / 2560)) (263434475667 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((232520333 / 125000000) : ℝ) ≤ Real.exp (3 * (331020767 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (331020767 / 100000000) / 16) (232520333 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3310415619 / 1000000000) : ℝ) / 16) ≤ (372047039 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3310415619 / 1000000000) / 16) (372047039 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1673 / 64000) : ℝ) (67 / 2560),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (331020767 / 100000000) (3310415619 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1673 / 64000) (67 / 2560) (526836023053 / 500000000000) (263434475667 / 250000000000) (331020767 / 100000000) (3310415619 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1673 / 64000) (67 / 2560) (331020767 / 100000000) (3310415619 / 1000000000) (24315561 / 500000000000) (48661471 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (331020767 / 100000000) (3310415619 / 1000000000) (232520333 / 125000000) (372047039 / 200000000) (24315561 / 500000000000) (48661471 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0415 :
    ∀ t ∈ Set.Icc ((67 / 2560) : ℝ) (1677 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1053737902667 / 1000000000000) : ℝ) ≤ Real.exp (2 * (67 / 2560)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (67 / 2560)) (1053737902667 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1677 / 64000) : ℝ)) ≤ (210760752669 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1677 / 64000)) (210760752669 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1860234827 / 1000000000) : ℝ) ≤ Real.exp (3 * (662082913 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (662082913 / 200000000) / 16) (1860234827 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3310622527 / 1000000000) : ℝ) / 16) ≤ (372061473 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3310622527 / 1000000000) / 16) (372061473 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((67 / 2560) : ℝ) (1677 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (662082913 / 200000000) (3310622527 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (67 / 2560) (1677 / 64000) (1053737902667 / 1000000000000) (210760752669 / 200000000000) (662082913 / 200000000) (3310622527 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (67 / 2560) (1677 / 64000) (662082913 / 200000000) (3310622527 / 1000000000) (3037559 / 62500000000) (48631277 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (662082913 / 200000000) (3310622527 / 1000000000) (1860234827 / 1000000000) (372061473 / 200000000) (3037559 / 62500000000) (48631277 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0416 :
    ∀ t ∈ Set.Icc ((1677 / 64000) : ℝ) (1679 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((65862735209 / 62500000000) : ℝ) ≤ Real.exp (2 * (1677 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1677 / 64000)) (65862735209 / 62500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1679 / 64000) : ℝ)) ≤ (1053869628139 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1679 / 64000)) (1053869628139 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((465076749 / 250000000) : ℝ) ≤ Real.exp (3 * (103456921 / 31250000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (103456921 / 31250000) / 16) (465076749 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3310829447 / 1000000000) : ℝ) / 16) ≤ (930189771 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3310829447 / 1000000000) / 16) (930189771 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1677 / 64000) : ℝ) (1679 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (103456921 / 31250000) (3310829447 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1677 / 64000) (1679 / 64000) (65862735209 / 62500000000) (1053869628139 / 1000000000000) (103456921 / 31250000) (3310829447 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1677 / 64000) (1679 / 64000) (103456921 / 31250000) (3310829447 / 1000000000) (1517837 / 31250000000) (486011 / 10000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (103456921 / 31250000) (3310829447 / 1000000000) (465076749 / 250000000) (930189771 / 500000000) (1517837 / 31250000000) (486011 / 10000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0417 :
    ∀ t ∈ Set.Icc ((1679 / 64000) : ℝ) (1681 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((526934814069 / 500000000000) : ℝ) ≤ Real.exp (2 * (1679 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1679 / 64000)) (526934814069 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1681 / 64000) : ℝ)) ≤ (1053935497049 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1681 / 64000)) (1053935497049 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1860379173 / 1000000000) : ℝ) ≤ Real.exp (3 * (413853549 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (413853549 / 125000000) / 16) (1860379173 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((165551819 / 50000000) : ℝ) / 16) ≤ (930225863 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (165551819 / 50000000) / 16) (930225863 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1679 / 64000) : ℝ) (1681 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (413853549 / 125000000) (165551819 / 50000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1679 / 64000) (1681 / 64000) (526934814069 / 500000000000) (1053935497049 / 1000000000000) (413853549 / 125000000) (165551819 / 50000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1679 / 64000) (1681 / 64000) (413853549 / 125000000) (165551819 / 50000000) (48540641 / 1000000000000) (48570939 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (413853549 / 125000000) (165551819 / 50000000) (1860379173 / 1000000000) (930225863 / 500000000) (48540641 / 1000000000000) (48570939 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0418 :
    ∀ t ∈ Set.Icc ((1681 / 64000) : ℝ) (1683 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((131741937131 / 125000000000) : ℝ) ≤ Real.exp (2 * (1681 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1681 / 64000)) (131741937131 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1683 / 64000) : ℝ)) ≤ (263500342519 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1683 / 64000)) (263500342519 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1860451357 / 1000000000) : ℝ) ≤ Real.exp (3 * (1655517663 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1655517663 / 500000000) / 16) (1860451357 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3311243327 / 1000000000) : ℝ) / 16) ≤ (1860523917 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3311243327 / 1000000000) / 16) (1860523917 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1681 / 64000) : ℝ) (1683 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1655517663 / 500000000) (3311243327 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1681 / 64000) (1683 / 64000) (131741937131 / 125000000000) (263500342519 / 250000000000) (1655517663 / 500000000) (3311243327 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1681 / 64000) (1683 / 64000) (1655517663 / 500000000) (3311243327 / 1000000000) (24255257 / 500000000000) (12135199 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1655517663 / 500000000) (3311243327 / 1000000000) (1860451357 / 1000000000) (1860523917 / 1000000000) (24255257 / 500000000000) (12135199 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0419 :
    ∀ t ∈ Set.Icc ((1683 / 64000) : ℝ) (337 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((42160054803 / 40000000000) : ℝ) ≤ Real.exp (2 * (1683 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1683 / 64000)) (42160054803 / 40000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((337 / 12800) : ℝ)) ≤ (52703362361 / 50000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (337 / 12800)) (52703362361 / 50000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((465130887 / 250000000) : ℝ) ≤ Real.exp (3 * (103476321 / 31250000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (103476321 / 31250000) / 16) (465130887 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1655725143 / 500000000) : ℝ) / 16) ≤ (465149029 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1655725143 / 500000000) / 16) (465149029 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1683 / 64000) : ℝ) (337 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (103476321 / 31250000) (1655725143 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1683 / 64000) (337 / 12800) (42160054803 / 40000000000) (52703362361 / 50000000000) (103476321 / 31250000) (1655725143 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1683 / 64000) (337 / 12800) (103476321 / 31250000) (1655725143 / 500000000) (9696081 / 200000000000) (48510669 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (103476321 / 31250000) (1655725143 / 500000000) (465130887 / 250000000) (465149029 / 250000000) (9696081 / 200000000000) (48510669 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch020 :
    ∀ t ∈ Set.Icc ((1649 / 64000) : ℝ) (337 / 12800),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0400
      hpThetaDensityTwoTermCompact_cell0401)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0402
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0403
      hpThetaDensityTwoTermCompact_cell0404)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0405
      hpThetaDensityTwoTermCompact_cell0406)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0407
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0408
      hpThetaDensityTwoTermCompact_cell0409))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0410
      hpThetaDensityTwoTermCompact_cell0411)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0412
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0413
      hpThetaDensityTwoTermCompact_cell0414)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0415
      hpThetaDensityTwoTermCompact_cell0416)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0417
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0418
      hpThetaDensityTwoTermCompact_cell0419)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch020
end HodgeProofHP
