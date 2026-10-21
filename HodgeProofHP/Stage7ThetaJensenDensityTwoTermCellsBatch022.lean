/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0440 :
    ∀ t ∈ Set.Icc ((69 / 2560) : ℝ) (1727 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1055385655111 / 1000000000000) : ℝ) ≤ Real.exp (2 * (69 / 2560)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (69 / 2560)) (1055385655111 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1727 / 64000) : ℝ)) ≤ (1055451618777 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1727 / 64000)) (1055451618777 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1862041259 / 1000000000) : ℝ) ≤ Real.exp (3 * (3315591131 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3315591131 / 1000000000) / 16) (1862041259 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1657899709 / 500000000) : ℝ) / 16) ≤ (1862113981 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1657899709 / 500000000) / 16) (1862113981 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((69 / 2560) : ℝ) (1727 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3315591131 / 1000000000) (1657899709 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (69 / 2560) (1727 / 64000) (1055385655111 / 1000000000000) (1055451618777 / 1000000000000) (3315591131 / 1000000000) (1657899709 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (69 / 2560) (1727 / 64000) (3315591131 / 1000000000) (1657899709 / 500000000) (4785197 / 100000000000) (47881881 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3315591131 / 1000000000) (1657899709 / 500000000) (1862041259 / 1000000000) (1862113981 / 1000000000) (4785197 / 100000000000) (47881881 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0441 :
    ∀ t ∈ Set.Icc ((1727 / 64000) : ℝ) (1729 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((131931452347 / 125000000000) : ℝ) ≤ Real.exp (2 * (1727 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1727 / 64000)) (131931452347 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1729 / 64000) : ℝ)) ≤ (211103517313 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1729 / 64000)) (211103517313 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1862113611 / 1000000000) : ℝ) ≤ Real.exp (3 * (3315798361 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3315798361 / 1000000000) / 16) (1862113611 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1658003331 / 500000000) : ℝ) / 16) ≤ (1862186341 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1658003331 / 500000000) / 16) (1862186341 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1727 / 64000) : ℝ) (1729 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3315798361 / 1000000000) (1658003331 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1727 / 64000) (1729 / 64000) (131931452347 / 125000000000) (211103517313 / 200000000000) (3315798361 / 1000000000) (1658003331 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1727 / 64000) (1729 / 64000) (3315798361 / 1000000000) (1658003331 / 500000000) (11955557 / 250000000000) (47852123 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3315798361 / 1000000000) (1658003331 / 500000000) (1862113611 / 1000000000) (1862186341 / 1000000000) (11955557 / 250000000000) (47852123 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0442 :
    ∀ t ∈ Set.Icc ((1729 / 64000) : ℝ) (1731 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((263879396641 / 250000000000) : ℝ) ≤ Real.exp (2 * (1729 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1729 / 64000)) (263879396641 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1731 / 64000) : ℝ)) ≤ (263895889619 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1731 / 64000)) (263895889619 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1862185971 / 1000000000) : ℝ) ≤ Real.exp (3 * (663201121 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (663201121 / 200000000) / 16) (1862185971 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3316213919 / 1000000000) : ℝ) / 16) ≤ (465564677 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3316213919 / 1000000000) / 16) (465564677 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1729 / 64000) : ℝ) (1731 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (663201121 / 200000000) (3316213919 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1729 / 64000) (1731 / 64000) (263879396641 / 250000000000) (263895889619 / 250000000000) (663201121 / 200000000) (3316213919 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1729 / 64000) (1731 / 64000) (663201121 / 200000000) (3316213919 / 1000000000) (47792503 / 1000000000000) (47822381 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (663201121 / 200000000) (3316213919 / 1000000000) (1862185971 / 1000000000) (465564677 / 250000000) (47792503 / 1000000000000) (47822381 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0443 :
    ∀ t ∈ Set.Icc ((1731 / 64000) : ℝ) (1733 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((42223342339 / 40000000000) : ℝ) ≤ Real.exp (2 * (1731 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1731 / 64000)) (42223342339 / 40000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1733 / 64000) : ℝ)) ≤ (105564953451 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1733 / 64000)) (105564953451 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((931129169 / 500000000) : ℝ) ≤ Real.exp (3 * (1658106431 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1658106431 / 500000000) / 16) (931129169 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3316421189 / 1000000000) : ℝ) / 16) ≤ (1862331083 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3316421189 / 1000000000) / 16) (1862331083 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1731 / 64000) : ℝ) (1733 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1658106431 / 500000000) (3316421189 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1731 / 64000) (1733 / 64000) (42223342339 / 40000000000) (105564953451 / 100000000000) (1658106431 / 500000000) (3316421189 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1731 / 64000) (1733 / 64000) (1658106431 / 500000000) (3316421189 / 1000000000) (23881397 / 500000000000) (2987041 / 62500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1658106431 / 500000000) (3316421189 / 1000000000) (931129169 / 500000000) (1862331083 / 1000000000) (23881397 / 500000000000) (2987041 / 62500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0444 :
    ∀ t ∈ Set.Icc ((1733 / 64000) : ℝ) (347 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1055649534509 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1733 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1733 / 64000)) (1055649534509 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((347 / 12800) : ℝ)) ≤ (1055715514667 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (347 / 12800)) (1055715514667 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((232791339 / 125000000) : ℝ) ≤ Real.exp (3 * (829105033 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (829105033 / 250000000) / 16) (232791339 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3316628471 / 1000000000) : ℝ) / 16) ≤ (232800433 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3316628471 / 1000000000) / 16) (232800433 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1733 / 64000) : ℝ) (347 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (829105033 / 250000000) (3316628471 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1733 / 64000) (347 / 12800) (1055649534509 / 1000000000000) (1055715514667 / 1000000000000) (829105033 / 250000000) (3316628471 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1733 / 64000) (347 / 12800) (829105033 / 250000000) (3316628471 / 1000000000) (47733103 / 1000000000000) (47762947 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (829105033 / 250000000) (3316628471 / 1000000000) (232791339 / 125000000) (232800433 / 125000000) (47733103 / 1000000000000) (47762947 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0445 :
    ∀ t ∈ Set.Icc ((347 / 12800) : ℝ) (1737 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((527857757333 / 500000000000) : ℝ) ≤ Real.exp (2 * (347 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (347 / 12800)) (527857757333 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1737 / 64000) : ℝ)) ≤ (1055781498949 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1737 / 64000)) (1055781498949 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((931201547 / 500000000) : ℝ) ≤ Real.exp (3 * (663325483 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (663325483 / 200000000) / 16) (931201547 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3316835767 / 1000000000) : ℝ) / 16) ≤ (1862475853 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3316835767 / 1000000000) / 16) (1862475853 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((347 / 12800) : ℝ) (1737 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (663325483 / 200000000) (3316835767 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (347 / 12800) (1737 / 64000) (527857757333 / 500000000000) (1055781498949 / 1000000000000) (663325483 / 200000000) (3316835767 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (347 / 12800) (1737 / 64000) (663325483 / 200000000) (3316835767 / 1000000000) (47703427 / 1000000000000) (9546651 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (663325483 / 200000000) (3316835767 / 1000000000) (931201547 / 500000000) (1862475853 / 1000000000) (47703427 / 1000000000000) (9546651 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0446 :
    ∀ t ∈ Set.Icc ((1737 / 64000) : ℝ) (1739 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((263945374737 / 250000000000) : ℝ) ≤ Real.exp (2 * (1737 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1737 / 64000)) (263945374737 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1739 / 64000) : ℝ)) ≤ (211169497471 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1739 / 64000)) (211169497471 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1862475483 / 1000000000) : ℝ) ≤ Real.exp (3 * (331683471 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (331683471 / 100000000) / 16) (1862475483 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((829260769 / 250000000) : ℝ) / 16) ≤ (7450193 / 4000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (829260769 / 250000000) / 16) (7450193 / 4000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1737 / 64000) : ℝ) (1739 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (331683471 / 100000000) (829260769 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1737 / 64000) (1739 / 64000) (263945374737 / 250000000000) (211169497471 / 200000000000) (331683471 / 100000000) (829260769 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1737 / 64000) (1739 / 64000) (331683471 / 100000000) (829260769 / 250000000) (5959221 / 125000000000) (2385179 / 50000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (331683471 / 100000000) (829260769 / 250000000) (1862475483 / 1000000000) (7450193 / 4000000) (5959221 / 125000000000) (2385179 / 50000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0447 :
    ∀ t ∈ Set.Icc ((1739 / 64000) : ℝ) (1741 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((527923743677 / 500000000000) : ℝ) ≤ Real.exp (2 * (1739 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1739 / 64000)) (527923743677 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1741 / 64000) : ℝ)) ≤ (211182695977 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1741 / 64000)) (211182695977 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((46563697 / 25000000) : ℝ) ≤ Real.exp (3 * (3317042019 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3317042019 / 1000000000) / 16) (46563697 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1658625199 / 500000000) : ℝ) / 16) ≤ (931310327 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1658625199 / 500000000) / 16) (931310327 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1739 / 64000) : ℝ) (1741 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3317042019 / 1000000000) (1658625199 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1739 / 64000) (1741 / 64000) (527923743677 / 500000000000) (211182695977 / 200000000000) (3317042019 / 1000000000) (1658625199 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1739 / 64000) (1741 / 64000) (3317042019 / 1000000000) (1658625199 / 500000000) (23822063 / 500000000000) (47673921 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3317042019 / 1000000000) (1658625199 / 500000000) (46563697 / 25000000) (931310327 / 500000000) (23822063 / 500000000000) (47673921 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0448 :
    ∀ t ∈ Set.Icc ((1741 / 64000) : ℝ) (1743 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((263978369971 / 250000000000) : ℝ) ≤ Real.exp (2 * (1741 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1741 / 64000)) (263978369971 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1743 / 64000) : ℝ)) ≤ (52798973827 / 50000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1743 / 64000)) (52798973827 / 50000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((465655071 / 250000000) : ℝ) ≤ Real.exp (3 * (3317249341 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3317249341 / 1000000000) / 16) (465655071 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((829364433 / 250000000) : ℝ) / 16) ≤ (372538613 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (829364433 / 250000000) / 16) (372538613 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1741 / 64000) : ℝ) (1743 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3317249341 / 1000000000) (829364433 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1741 / 64000) (1743 / 64000) (263978369971 / 250000000000) (52798973827 / 50000000000) (3317249341 / 1000000000) (829364433 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1741 / 64000) (1743 / 64000) (3317249341 / 1000000000) (829364433 / 250000000) (47614501 / 1000000000000) (23822139 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3317249341 / 1000000000) (829364433 / 250000000) (465655071 / 250000000) (372538613 / 200000000) (47614501 / 1000000000000) (23822139 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0449 :
    ∀ t ∈ Set.Icc ((1743 / 64000) : ℝ) (349 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1055979476539 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1743 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1743 / 64000)) (1055979476539 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((349 / 12800) : ℝ)) ≤ (26401136933 / 25000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (349 / 12800)) (26401136933 / 25000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((372538539 / 200000000) : ℝ) ≤ Real.exp (3 * (132698267 / 40000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (132698267 / 40000000) / 16) (372538539 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((82941627 / 25000000) : ℝ) / 16) ≤ (465691371 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (82941627 / 25000000) / 16) (465691371 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1743 / 64000) : ℝ) (349 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (132698267 / 40000000) (82941627 / 25000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1743 / 64000) (349 / 12800) (1055979476539 / 1000000000000) (26401136933 / 25000000000) (132698267 / 40000000) (82941627 / 25000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1743 / 64000) (349 / 12800) (132698267 / 40000000) (82941627 / 25000000) (47584891 / 1000000000000) (47614653 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (132698267 / 40000000) (82941627 / 25000000) (372538539 / 200000000) (465691371 / 250000000) (47584891 / 1000000000000) (47614653 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0450 :
    ∀ t ∈ Set.Icc ((349 / 12800) : ℝ) (1747 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1056045477319 / 1000000000000) : ℝ) ≤ Real.exp (2 * (349 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (349 / 12800)) (1056045477319 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1747 / 64000) : ℝ)) ≤ (42244459289 / 40000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1747 / 64000)) (42244459289 / 40000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((931382557 / 500000000) : ℝ) ≤ Real.exp (3 * (3317664023 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3317664023 / 1000000000) / 16) (931382557 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((82946811 / 25000000) : ℝ) / 16) ≤ (186283791 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (82946811 / 25000000) / 16) (186283791 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((349 / 12800) : ℝ) (1747 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3317664023 / 1000000000) (82946811 / 25000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (349 / 12800) (1747 / 64000) (1056045477319 / 1000000000000) (42244459289 / 40000000000) (3317664023 / 1000000000) (82946811 / 25000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (349 / 12800) (1747 / 64000) (3317664023 / 1000000000) (82946811 / 25000000) (47555299 / 1000000000000) (11896261 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3317664023 / 1000000000) (82946811 / 25000000) (931382557 / 500000000) (186283791 / 100000000) (47555299 / 1000000000000) (11896261 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0451 :
    ∀ t ∈ Set.Icc ((1747 / 64000) : ℝ) (1749 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((66006967639 / 62500000000) : ℝ) ≤ Real.exp (2 * (1747 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1747 / 64000)) (66006967639 / 62500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1749 / 64000) : ℝ)) ≤ (211235498251 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1749 / 64000)) (211235498251 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1862837539 / 1000000000) : ℝ) ≤ Real.exp (3 * (3317871383 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3317871383 / 1000000000) / 16) (1862837539 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1659039907 / 500000000) : ℝ) / 16) ≤ (1862910343 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1659039907 / 500000000) / 16) (1862910343 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1747 / 64000) : ℝ) (1749 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3317871383 / 1000000000) (1659039907 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1747 / 64000) (1749 / 64000) (66006967639 / 62500000000) (211235498251 / 200000000000) (3317871383 / 1000000000) (1659039907 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1747 / 64000) (1749 / 64000) (3317871383 / 1000000000) (1659039907 / 500000000) (47525723 / 1000000000000) (47555451 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3317871383 / 1000000000) (1659039907 / 500000000) (1862837539 / 1000000000) (1862910343 / 1000000000) (47525723 / 1000000000000) (47555451 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0452 :
    ∀ t ∈ Set.Icc ((1749 / 64000) : ℝ) (1751 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((528088745627 / 500000000000) : ℝ) ≤ Real.exp (2 * (1749 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1749 / 64000)) (528088745627 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1751 / 64000) : ℝ)) ≤ (1056243504411 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1751 / 64000)) (1056243504411 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1862909973 / 1000000000) : ℝ) ≤ Real.exp (3 * (3318078757 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3318078757 / 1000000000) / 16) (1862909973 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((4147859 / 1250000) : ℝ) / 16) ≤ (1862982783 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (4147859 / 1250000) / 16) (1862982783 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1749 / 64000) : ℝ) (1751 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3318078757 / 1000000000) (4147859 / 1250000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1749 / 64000) (1751 / 64000) (528088745627 / 500000000000) (1056243504411 / 1000000000000) (3318078757 / 1000000000) (4147859 / 1250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1749 / 64000) (1751 / 64000) (3318078757 / 1000000000) (4147859 / 1250000) (11874041 / 250000000000) (380207 / 8000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3318078757 / 1000000000) (4147859 / 1250000) (1862909973 / 1000000000) (1862982783 / 1000000000) (11874041 / 250000000000) (380207 / 8000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0453 :
    ∀ t ∈ Set.Icc ((1751 / 64000) : ℝ) (1753 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((105624350441 / 100000000000) : ℝ) ≤ Real.exp (2 * (1751 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1751 / 64000)) (105624350441 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1753 / 64000) : ℝ)) ≤ (1056309521693 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1753 / 64000)) (1056309521693 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1862982413 / 1000000000) : ℝ) ≤ Real.exp (3 * (3318286143 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3318286143 / 1000000000) / 16) (1862982413 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((16592473 / 5000000) : ℝ) / 16) ≤ (14555119 / 7812500) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (16592473 / 5000000) / 16) (14555119 / 7812500) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1751 / 64000) : ℝ) (1753 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3318286143 / 1000000000) (16592473 / 5000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1751 / 64000) (1753 / 64000) (105624350441 / 100000000000) (1056309521693 / 1000000000000) (3318286143 / 1000000000) (16592473 / 5000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1751 / 64000) (1753 / 64000) (3318286143 / 1000000000) (16592473 / 5000000) (47466621 / 1000000000000) (11874079 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3318286143 / 1000000000) (16592473 / 5000000) (1862982413 / 1000000000) (14555119 / 7812500) (47466621 / 1000000000000) (11874079 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0454 :
    ∀ t ∈ Set.Icc ((1753 / 64000) : ℝ) (351 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((264077380423 / 250000000000) : ℝ) ≤ Real.exp (2 * (1753 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1753 / 64000)) (264077380423 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((351 / 12800) : ℝ)) ≤ (528187771551 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (351 / 12800)) (528187771551 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1863054861 / 1000000000) : ℝ) ≤ Real.exp (3 * (1659246771 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1659246771 / 500000000) / 16) (1863054861 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((829675503 / 250000000) : ℝ) / 16) ≤ (1863127687 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (829675503 / 250000000) / 16) (1863127687 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1753 / 64000) : ℝ) (351 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1659246771 / 500000000) (829675503 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1753 / 64000) (351 / 12800) (264077380423 / 250000000000) (528187771551 / 500000000000) (1659246771 / 500000000) (829675503 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1753 / 64000) (351 / 12800) (1659246771 / 500000000) (829675503 / 250000000) (23718547 / 500000000000) (47466773 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1659246771 / 500000000) (829675503 / 250000000) (1863054861 / 1000000000) (1863127687 / 1000000000) (23718547 / 500000000000) (47466773 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0455 :
    ∀ t ∈ Set.Icc ((351 / 12800) : ℝ) (1757 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1056375543101 / 1000000000000) : ℝ) ≤ Real.exp (2 * (351 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (351 / 12800)) (1056375543101 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1757 / 64000) : ℝ)) ≤ (264110392159 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1757 / 64000)) (264110392159 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((465781829 / 250000000) : ℝ) ≤ Real.exp (3 * (663740191 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (663740191 / 200000000) / 16) (465781829 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3318909437 / 1000000000) : ℝ) / 16) ≤ (1863200149 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3318909437 / 1000000000) / 16) (1863200149 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((351 / 12800) : ℝ) (1757 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (663740191 / 200000000) (3318909437 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (351 / 12800) (1757 / 64000) (1056375543101 / 1000000000000) (264110392159 / 250000000000) (663740191 / 200000000) (3318909437 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (351 / 12800) (1757 / 64000) (663740191 / 200000000) (3318909437 / 1000000000) (9481517 / 200000000000) (47437247 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (663740191 / 200000000) (3318909437 / 1000000000) (465781829 / 250000000) (1863200149 / 1000000000) (9481517 / 200000000000) (47437247 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0456 :
    ∀ t ∈ Set.Icc ((1757 / 64000) : ℝ) (1759 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((211288313727 / 200000000000) : ℝ) ≤ Real.exp (2 * (1757 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1757 / 64000)) (211288313727 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1759 / 64000) : ℝ)) ≤ (528253799149 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1759 / 64000)) (528253799149 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1863199779 / 1000000000) : ℝ) ≤ Real.exp (3 * (165945419 / 50000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (165945419 / 50000000) / 16) (1863199779 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((829779219 / 250000000) : ℝ) / 16) ≤ (93163631 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (829779219 / 250000000) / 16) (93163631 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1757 / 64000) : ℝ) (1759 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (165945419 / 50000000) (829779219 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1757 / 64000) (1759 / 64000) (211288313727 / 200000000000) (528253799149 / 500000000000) (165945419 / 50000000) (829779219 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1757 / 64000) (1759 / 64000) (165945419 / 50000000) (829779219 / 250000000) (47378091 / 1000000000000) (47407737 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (165945419 / 50000000) (829779219 / 250000000) (1863199779 / 1000000000) (93163631 / 50000000) (47378091 / 1000000000000) (47407737 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0457 :
    ∀ t ∈ Set.Icc ((1759 / 64000) : ℝ) (1761 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1056507598297 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1759 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1759 / 64000)) (1056507598297 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1761 / 64000) : ℝ)) ≤ (528286816043 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1761 / 64000)) (528286816043 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1863272249 / 1000000000) : ℝ) ≤ Real.exp (3 * (1659557909 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1659557909 / 500000000) / 16) (1863272249 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3319324327 / 1000000000) : ℝ) / 16) ≤ (1863345097 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3319324327 / 1000000000) / 16) (1863345097 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1759 / 64000) : ℝ) (1761 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1659557909 / 500000000) (3319324327 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1759 / 64000) (1761 / 64000) (1056507598297 / 1000000000000) (528286816043 / 500000000000) (1659557909 / 500000000) (3319324327 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1759 / 64000) (1761 / 64000) (1659557909 / 500000000) (3319324327 / 1000000000) (9469723 / 200000000000) (47378243 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1659557909 / 500000000) (3319324327 / 1000000000) (1863272249 / 1000000000) (1863345097 / 1000000000) (9469723 / 200000000000) (47378243 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0458 :
    ∀ t ∈ Set.Icc ((1761 / 64000) : ℝ) (1763 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((211314726417 / 200000000000) : ℝ) ≤ Real.exp (2 * (1761 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1761 / 64000)) (211314726417 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1763 / 64000) : ℝ)) ≤ (528319835001 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1763 / 64000)) (528319835001 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((931672363 / 500000000) : ℝ) ≤ Real.exp (3 * (3319323269 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3319323269 / 1000000000) / 16) (931672363 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3319531791 / 1000000000) : ℝ) / 16) ≤ (1863417581 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3319531791 / 1000000000) / 16) (1863417581 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1761 / 64000) : ℝ) (1763 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3319323269 / 1000000000) (3319531791 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1761 / 64000) (1763 / 64000) (211314726417 / 200000000000) (528319835001 / 500000000000) (3319323269 / 1000000000) (3319531791 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1761 / 64000) (1763 / 64000) (3319323269 / 1000000000) (3319531791 / 1000000000) (9463831 / 200000000000) (23674383 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3319323269 / 1000000000) (3319531791 / 1000000000) (931672363 / 500000000) (1863417581 / 1000000000) (9463831 / 200000000000) (23674383 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0459 :
    ∀ t ∈ Set.Icc ((1763 / 64000) : ℝ) (353 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1056639670001 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1763 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1763 / 64000)) (1056639670001 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((353 / 12800) : ℝ)) ≤ (211341142409 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (353 / 12800)) (211341142409 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1863417211 / 1000000000) : ℝ) ≤ Real.exp (3 * (1659765367 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1659765367 / 500000000) / 16) (1863417211 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3319739269 / 1000000000) : ℝ) / 16) ≤ (931745037 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3319739269 / 1000000000) / 16) (931745037 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1763 / 64000) : ℝ) (353 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1659765367 / 500000000) (3319739269 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1763 / 64000) (353 / 12800) (1056639670001 / 1000000000000) (211341142409 / 200000000000) (1659765367 / 500000000) (3319739269 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1763 / 64000) (353 / 12800) (1659765367 / 500000000) (3319739269 / 1000000000) (4728971 / 100000000000) (23659653 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1659765367 / 500000000) (3319739269 / 1000000000) (1863417211 / 1000000000) (931745037 / 500000000) (4728971 / 100000000000) (23659653 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch022 :
    ∀ t ∈ Set.Icc ((69 / 2560) : ℝ) (353 / 12800),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0440
      hpThetaDensityTwoTermCompact_cell0441)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0442
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0443
      hpThetaDensityTwoTermCompact_cell0444)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0445
      hpThetaDensityTwoTermCompact_cell0446)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0447
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0448
      hpThetaDensityTwoTermCompact_cell0449))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0450
      hpThetaDensityTwoTermCompact_cell0451)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0452
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0453
      hpThetaDensityTwoTermCompact_cell0454)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0455
      hpThetaDensityTwoTermCompact_cell0456)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0457
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0458
      hpThetaDensityTwoTermCompact_cell0459)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch022
end HodgeProofHP
