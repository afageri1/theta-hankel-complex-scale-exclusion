/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0140 :
    ∀ t ∈ Set.Icc ((1389 / 64000) : ℝ) (139 / 6400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1044362080777 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1389 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1389 / 64000)) (1044362080777 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((139 / 6400) : ℝ)) ≤ (1044394717603 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (139 / 6400)) (1044394717603 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((924994707 / 500000000) : ℝ) ≤ Real.exp (3 * (1640479779 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1640479779 / 500000000) / 16) (924994707 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((656212627 / 200000000) : ℝ) / 16) ≤ (1850025343 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (656212627 / 200000000) / 16) (1850025343 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1389 / 64000) : ℝ) (139 / 6400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1640479779 / 500000000) (656212627 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1389 / 64000) (139 / 6400) (1044362080777 / 1000000000000) (1044394717603 / 1000000000000) (1640479779 / 500000000) (656212627 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1389 / 64000) (139 / 6400) (1640479779 / 500000000) (656212627 / 200000000) (26553829 / 500000000000) (13281041 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1640479779 / 500000000) (656212627 / 200000000) (924994707 / 500000000) (1850025343 / 1000000000) (26553829 / 500000000000) (13281041 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0141 :
    ∀ t ∈ Set.Icc ((139 / 6400) : ℝ) (1391 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((522197358801 / 500000000000) : ℝ) ≤ Real.exp (2 * (139 / 6400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (139 / 6400)) (522197358801 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1391 / 64000) : ℝ)) ≤ (130553419431 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1391 / 64000)) (130553419431 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1850024979 / 1000000000) : ℝ) ≤ Real.exp (3 * (3281062089 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3281062089 / 1000000000) / 16) (1850024979 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3281165669 / 1000000000) : ℝ) / 16) ≤ (1850060911 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3281165669 / 1000000000) / 16) (1850060911 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((139 / 6400) : ℝ) (1391 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3281062089 / 1000000000) (3281165669 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (139 / 6400) (1391 / 64000) (522197358801 / 500000000000) (130553419431 / 125000000000) (3281062089 / 1000000000) (3281165669 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (139 / 6400) (1391 / 64000) (3281062089 / 1000000000) (3281165669 / 1000000000) (13272831 / 250000000000) (26553913 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3281062089 / 1000000000) (3281165669 / 1000000000) (1850024979 / 1000000000) (1850060911 / 1000000000) (13272831 / 250000000000) (26553913 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0142 :
    ∀ t ∈ Set.Icc ((1391 / 64000) : ℝ) (87 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1044427355447 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1391 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1391 / 64000)) (1044427355447 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((87 / 4000) : ℝ)) ≤ (1044459994313 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (87 / 4000)) (1044459994313 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1850060547 / 1000000000) : ℝ) ≤ Real.exp (3 * (205072789 / 62500000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (205072789 / 62500000) / 16) (1850060547 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3281268207 / 1000000000) : ℝ) / 16) ≤ (11563103 / 6250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3281268207 / 1000000000) / 16) (11563103 / 6250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1391 / 64000) : ℝ) (87 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (205072789 / 62500000) (3281268207 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1391 / 64000) (87 / 4000) (1044427355447 / 1000000000000) (1044459994313 / 1000000000000) (205072789 / 62500000) (3281268207 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1391 / 64000) (87 / 4000) (205072789 / 62500000) (3281268207 / 1000000000) (13268749 / 250000000000) (53091493 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (205072789 / 62500000) (3281268207 / 1000000000) (1850060547 / 1000000000) (11563103 / 6250000) (13268749 / 250000000000) (53091493 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0143 :
    ∀ t ∈ Set.Icc ((87 / 4000) : ℝ) (1393 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((130557499289 / 125000000000) : ℝ) ≤ Real.exp (2 * (87 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (87 / 4000)) (130557499289 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1393 / 64000) : ℝ)) ≤ (1044492634197 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1393 / 64000)) (1044492634197 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((462524029 / 250000000) : ℝ) ≤ Real.exp (3 * (1640633581 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1640633581 / 500000000) / 16) (462524029 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3281370749 / 1000000000) : ℝ) / 16) ≤ (1850132051 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3281370749 / 1000000000) / 16) (1850132051 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((87 / 4000) : ℝ) (1393 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1640633581 / 500000000) (3281370749 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (87 / 4000) (1393 / 64000) (130557499289 / 125000000000) (1044492634197 / 1000000000000) (1640633581 / 500000000) (3281370749 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (87 / 4000) (1393 / 64000) (1640633581 / 500000000) (3281370749 / 1000000000) (53058671 / 1000000000000) (13268791 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1640633581 / 500000000) (3281370749 / 1000000000) (462524029 / 250000000) (1850132051 / 1000000000) (53058671 / 1000000000000) (13268791 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0144 :
    ∀ t ∈ Set.Icc ((1393 / 64000) : ℝ) (697 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((261123158549 / 250000000000) : ℝ) ≤ Real.exp (2 * (1393 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1393 / 64000)) (261123158549 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((697 / 32000) : ℝ)) ≤ (522262637551 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (697 / 32000)) (522262637551 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((231266461 / 125000000) : ℝ) ≤ Real.exp (3 * (3281369703 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3281369703 / 1000000000) / 16) (231266461 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3281473293 / 1000000000) : ℝ) / 16) ≤ (231270953 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3281473293 / 1000000000) / 16) (231270953 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1393 / 64000) : ℝ) (697 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3281369703 / 1000000000) (3281473293 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1393 / 64000) (697 / 32000) (261123158549 / 250000000000) (522262637551 / 500000000000) (3281369703 / 1000000000) (3281473293 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1393 / 64000) (697 / 32000) (3281369703 / 1000000000) (3281473293 / 1000000000) (53042351 / 1000000000000) (53058839 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3281369703 / 1000000000) (3281473293 / 1000000000) (231266461 / 125000000) (231270953 / 125000000) (53042351 / 1000000000000) (53058839 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0145 :
    ∀ t ∈ Set.Icc ((697 / 32000) : ℝ) (279 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1044525275101 / 1000000000000) : ℝ) ≤ Real.exp (2 * (697 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (697 / 32000)) (1044525275101 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((279 / 12800) : ℝ)) ≤ (1044557917027 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (279 / 12800)) (1044557917027 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1850167261 / 1000000000) : ℝ) ≤ Real.exp (3 * (410184031 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (410184031 / 125000000) / 16) (1850167261 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3281575841 / 1000000000) : ℝ) / 16) ≤ (1850203199 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3281575841 / 1000000000) / 16) (1850203199 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((697 / 32000) : ℝ) (279 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (410184031 / 125000000) (3281575841 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (697 / 32000) (279 / 12800) (1044525275101 / 1000000000000) (1044557917027 / 1000000000000) (410184031 / 125000000) (3281575841 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (697 / 32000) (279 / 12800) (410184031 / 125000000) (3281575841 / 1000000000) (10605207 / 200000000000) (26521259 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (410184031 / 125000000) (3281575841 / 1000000000) (1850167261 / 1000000000) (1850203199 / 1000000000) (10605207 / 200000000000) (26521259 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0146 :
    ∀ t ∈ Set.Icc ((279 / 12800) : ℝ) (349 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((522278958513 / 500000000000) : ℝ) ≤ Real.exp (2 * (279 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (279 / 12800)) (522278958513 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((349 / 16000) : ℝ)) ≤ (261147639993 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (349 / 16000)) (261147639993 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((370040567 / 200000000) : ℝ) ≤ Real.exp (3 * (656314959 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (656314959 / 200000000) / 16) (370040567 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((410209799 / 125000000) : ℝ) / 16) ≤ (231279847 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (410209799 / 125000000) / 16) (231279847 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((279 / 12800) : ℝ) (349 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (656314959 / 200000000) (410209799 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (279 / 12800) (349 / 16000) (522278958513 / 500000000000) (261147639993 / 250000000000) (656314959 / 200000000) (410209799 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (279 / 12800) (349 / 16000) (656314959 / 200000000) (410209799 / 125000000) (13252431 / 250000000000) (53026203 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (656314959 / 200000000) (410209799 / 125000000) (370040567 / 200000000) (231279847 / 125000000) (13252431 / 250000000000) (53026203 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0147 :
    ∀ t ∈ Set.Icc ((349 / 16000) : ℝ) (1397 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1044590559971 / 1000000000000) : ℝ) ≤ Real.exp (2 * (349 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (349 / 16000)) (1044590559971 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1397 / 64000) : ℝ)) ≤ (1044623203937 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1397 / 64000)) (1044623203937 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((462559603 / 250000000) : ℝ) ≤ Real.exp (3 * (1640838673 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1640838673 / 500000000) / 16) (462559603 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1640890473 / 500000000) : ℝ) / 16) ≤ (925137177 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1640890473 / 500000000) / 16) (925137177 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((349 / 16000) : ℝ) (1397 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1640838673 / 500000000) (1640890473 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (349 / 16000) (1397 / 64000) (1044590559971 / 1000000000000) (1044623203937 / 1000000000000) (1640838673 / 500000000) (1640890473 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (349 / 16000) (1397 / 64000) (1640838673 / 500000000) (1640890473 / 500000000) (52993417 / 1000000000000) (13252473 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1640838673 / 500000000) (1640890473 / 500000000) (462559603 / 250000000) (925137177 / 500000000) (52993417 / 1000000000000) (13252473 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0148 :
    ∀ t ∈ Set.Icc ((1397 / 64000) : ℝ) (699 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((32644475123 / 31250000000) : ℝ) ≤ Real.exp (2 * (1397 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1397 / 64000)) (32644475123 / 31250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((699 / 32000) : ℝ)) ≤ (522327924461 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (699 / 32000)) (522327924461 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((185027399 / 100000000) : ℝ) ≤ Real.exp (3 * (32817799 / 10000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (32817799 / 10000000) / 16) (185027399 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3281883503 / 1000000000) : ℝ) / 16) ≤ (925154967 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3281883503 / 1000000000) / 16) (925154967 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1397 / 64000) : ℝ) (699 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (32817799 / 10000000) (3281883503 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1397 / 64000) (699 / 32000) (32644475123 / 31250000000) (522327924461 / 500000000000) (32817799 / 10000000) (3281883503 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1397 / 64000) (699 / 32000) (32817799 / 10000000) (3281883503 / 1000000000) (13244279 / 250000000000) (10598717 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (32817799 / 10000000) (3281883503 / 1000000000) (185027399 / 100000000) (925154967 / 500000000) (13244279 / 250000000000) (10598717 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0149 :
    ∀ t ∈ Set.Icc ((699 / 32000) : ℝ) (1399 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1044655848921 / 1000000000000) : ℝ) ≤ Real.exp (2 * (699 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (699 / 32000)) (1044655848921 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1399 / 64000) : ℝ)) ≤ (65293030933 / 62500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1399 / 64000)) (65293030933 / 62500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((185030957 / 100000000) : ℝ) ≤ Real.exp (3 * (3281882457 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3281882457 / 1000000000) / 16) (185030957 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3281986063 / 1000000000) : ℝ) / 16) ≤ (462586379 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3281986063 / 1000000000) / 16) (462586379 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((699 / 32000) : ℝ) (1399 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3281882457 / 1000000000) (3281986063 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (699 / 32000) (1399 / 64000) (1044655848921 / 1000000000000) (65293030933 / 62500000000) (3281882457 / 1000000000) (3281986063 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (699 / 32000) (1399 / 64000) (3281882457 / 1000000000) (3281986063 / 1000000000) (26480409 / 500000000000) (52977283 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3281882457 / 1000000000) (3281986063 / 1000000000) (185030957 / 100000000) (462586379 / 250000000) (26480409 / 500000000000) (52977283 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0150 :
    ∀ t ∈ Set.Icc ((1399 / 64000) : ℝ) (7 / 320), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1044688494927 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1399 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1399 / 64000)) (1044688494927 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((7 / 320) : ℝ)) ≤ (1044721141953 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (7 / 320)) (1044721141953 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((28911643 / 15625000) : ℝ) ≤ Real.exp (3 * (1640992509 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1640992509 / 500000000) / 16) (28911643 / 15625000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3282088627 / 1000000000) : ℝ) / 16) ≤ (18503811 / 10000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3282088627 / 1000000000) / 16) (18503811 / 10000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1399 / 64000) : ℝ) (7 / 320),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1640992509 / 500000000) (3282088627 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1399 / 64000) (7 / 320) (1044688494927 / 1000000000000) (1044721141953 / 1000000000000) (1640992509 / 500000000) (3282088627 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1399 / 64000) (7 / 320) (1640992509 / 500000000) (3282088627 / 1000000000) (2117781 / 40000000000) (26480493 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1640992509 / 500000000) (3282088627 / 1000000000) (28911643 / 15625000) (18503811 / 10000000) (2117781 / 40000000000) (26480493 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0151 :
    ∀ t ∈ Set.Icc ((7 / 320) : ℝ) (1401 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((16323767843 / 15625000000) : ℝ) ≤ Real.exp (2 * (7 / 320)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (7 / 320)) (16323767843 / 15625000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1401 / 64000) : ℝ)) ≤ (1044753789999 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1401 / 64000)) (1044753789999 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((28912199 / 15625000) : ℝ) ≤ Real.exp (3 * (3282087581 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3282087581 / 1000000000) / 16) (28912199 / 15625000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1641095597 / 500000000) : ℝ) / 16) ≤ (925208343 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1641095597 / 500000000) / 16) (925208343 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((7 / 320) : ℝ) (1401 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3282087581 / 1000000000) (1641095597 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (7 / 320) (1401 / 64000) (16323767843 / 15625000000) (1044753789999 / 1000000000000) (3282087581 / 1000000000) (1641095597 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (7 / 320) (1401 / 64000) (3282087581 / 1000000000) (1641095597 / 500000000) (13232059 / 250000000000) (13236173 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3282087581 / 1000000000) (1641095597 / 500000000) (28912199 / 15625000) (925208343 / 500000000) (13232059 / 250000000000) (13236173 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0152 :
    ∀ t ∈ Set.Icc ((1401 / 64000) : ℝ) (701 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((522376894999 / 500000000000) : ℝ) ≤ Real.exp (2 * (1401 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1401 / 64000)) (522376894999 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((701 / 32000) : ℝ)) ≤ (208957287813 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (701 / 32000)) (208957287813 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((925208161 / 500000000) : ℝ) ≤ Real.exp (3 * (820547537 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (820547537 / 250000000) / 16) (925208161 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((820573441 / 250000000) : ℝ) / 16) ≤ (1850452273 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (820573441 / 250000000) / 16) (1850452273 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1401 / 64000) : ℝ) (701 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (820547537 / 250000000) (820573441 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1401 / 64000) (701 / 32000) (522376894999 / 500000000000) (208957287813 / 200000000000) (820547537 / 250000000) (820573441 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1401 / 64000) (701 / 32000) (820547537 / 250000000) (820573441 / 250000000) (3306997 / 62500000000) (13232101 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (820547537 / 250000000) (820573441 / 250000000) (925208161 / 500000000) (1850452273 / 1000000000) (3306997 / 62500000000) (13232101 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0153 :
    ∀ t ∈ Set.Icc ((701 / 32000) : ℝ) (1403 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((130598304883 / 125000000000) : ℝ) ≤ Real.exp (2 * (701 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (701 / 32000)) (130598304883 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1403 / 64000) : ℝ)) ≤ (1044819089151 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1403 / 64000)) (1044819089151 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1850451909 / 1000000000) : ℝ) ≤ Real.exp (3 * (1641146359 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1641146359 / 500000000) / 16) (1850451909 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3282396337 / 1000000000) : ℝ) / 16) ≤ (925243931 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3282396337 / 1000000000) / 16) (925243931 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((701 / 32000) : ℝ) (1403 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1641146359 / 500000000) (3282396337 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (701 / 32000) (1403 / 64000) (130598304883 / 125000000000) (1044819089151 / 1000000000000) (1641146359 / 500000000) (3282396337 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (701 / 32000) (1403 / 64000) (1641146359 / 500000000) (3282396337 / 1000000000) (52895673 / 1000000000000) (1322803 / 25000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1641146359 / 500000000) (3282396337 / 1000000000) (1850451909 / 1000000000) (925243931 / 500000000) (52895673 / 1000000000000) (1322803 / 25000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0154 :
    ∀ t ∈ Set.Icc ((1403 / 64000) : ℝ) (351 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((20896381783 / 20000000000) : ℝ) ≤ Real.exp (2 * (1403 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1403 / 64000)) (20896381783 / 20000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((351 / 16000) : ℝ)) ≤ (522425870129 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (351 / 16000)) (522425870129 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((925243749 / 500000000) : ℝ) ≤ Real.exp (3 * (3282395291 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3282395291 / 1000000000) / 16) (925243749 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1641249457 / 500000000) : ℝ) / 16) ≤ (1850523453 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1641249457 / 500000000) / 16) (1850523453 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1403 / 64000) : ℝ) (351 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3282395291 / 1000000000) (1641249457 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1403 / 64000) (351 / 16000) (20896381783 / 20000000000) (522425870129 / 500000000000) (3282395291 / 1000000000) (1641249457 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1403 / 64000) (351 / 16000) (3282395291 / 1000000000) (1641249457 / 500000000) (26439699 / 500000000000) (330599 / 6250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3282395291 / 1000000000) (1641249457 / 500000000) (925243749 / 500000000) (1850523453 / 1000000000) (26439699 / 500000000000) (330599 / 6250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0155 :
    ∀ t ∈ Set.Icc ((351 / 16000) : ℝ) (281 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1044851740257 / 1000000000000) : ℝ) ≤ Real.exp (2 * (351 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (351 / 16000)) (1044851740257 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((281 / 12800) : ℝ)) ≤ (208976878477 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (281 / 12800)) (208976878477 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1850523089 / 1000000000) : ℝ) ≤ Real.exp (3 * (820624467 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (820624467 / 250000000) / 16) (1850523089 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3282601493 / 1000000000) : ℝ) / 16) ≤ (925279523 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3282601493 / 1000000000) / 16) (925279523 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((351 / 16000) : ℝ) (281 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (820624467 / 250000000) (3282601493 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (351 / 16000) (281 / 12800) (1044851740257 / 1000000000000) (208976878477 / 200000000000) (820624467 / 250000000) (3282601493 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (351 / 16000) (281 / 12800) (820624467 / 250000000) (3282601493 / 1000000000) (52863127 / 1000000000000) (10575913 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (820624467 / 250000000) (3282601493 / 1000000000) (1850523089 / 1000000000) (925279523 / 500000000) (52863127 / 1000000000000) (10575913 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0156 :
    ∀ t ∈ Set.Icc ((281 / 12800) : ℝ) (703 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((16326318631 / 15625000000) : ℝ) ≤ Real.exp (2 * (281 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (281 / 12800)) (16326318631 / 15625000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((703 / 32000) : ℝ)) ≤ (1044917045533 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (703 / 32000)) (1044917045533 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((925279341 / 500000000) : ℝ) ≤ Real.exp (3 * (6411329 / 1953125) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6411329 / 1953125) / 16) (925279341 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((820676019 / 250000000) : ℝ) / 16) ≤ (23132433 / 12500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (820676019 / 250000000) / 16) (23132433 / 12500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((281 / 12800) : ℝ) (703 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6411329 / 1953125) (820676019 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (281 / 12800) (703 / 32000) (16326318631 / 15625000000) (1044917045533 / 1000000000000) (6411329 / 1953125) (820676019 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (281 / 12800) (703 / 32000) (6411329 / 1953125) (820676019 / 250000000) (52846861 / 1000000000000) (26431647 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (6411329 / 1953125) (820676019 / 250000000) (925279341 / 500000000) (23132433 / 12500000) (52846861 / 1000000000000) (26431647 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0157 :
    ∀ t ∈ Set.Icc ((703 / 32000) : ℝ) (1407 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((261229261383 / 250000000000) : ℝ) ≤ Real.exp (2 * (703 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (703 / 32000)) (261229261383 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1407 / 64000) : ℝ)) ≤ (1044949699701 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1407 / 64000)) (1044949699701 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((462648569 / 250000000) : ℝ) ≤ Real.exp (3 * (328270303 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (328270303 / 100000000) / 16) (462648569 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1641403331 / 500000000) : ℝ) / 16) ≤ (462657559 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1641403331 / 500000000) / 16) (462657559 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((703 / 32000) : ℝ) (1407 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (328270303 / 100000000) (1641403331 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (703 / 32000) (1407 / 64000) (261229261383 / 250000000000) (1044949699701 / 1000000000000) (328270303 / 100000000) (1641403331 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (703 / 32000) (1407 / 64000) (328270303 / 100000000) (1641403331 / 500000000) (264153 / 5000000000) (13211757 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (328270303 / 100000000) (1641403331 / 500000000) (462648569 / 250000000) (462657559 / 250000000) (264153 / 5000000000) (13211757 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0158 :
    ∀ t ∈ Set.Icc ((1407 / 64000) : ℝ) (11 / 500), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((10449496997 / 10000000000) : ℝ) ≤ Real.exp (2 * (1407 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1407 / 64000)) (10449496997 / 10000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((11 / 500) : ℝ)) ≤ (1044982354889 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (11 / 500)) (1044982354889 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((115664367 / 62500000) : ℝ) ≤ Real.exp (3 * (205175351 / 62500000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (205175351 / 62500000) / 16) (115664367 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((820727313 / 250000000) : ℝ) / 16) ≤ (370133167 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (820727313 / 250000000) / 16) (370133167 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1407 / 64000) : ℝ) (11 / 500),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (205175351 / 62500000) (820727313 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1407 / 64000) (11 / 500) (10449496997 / 10000000000) (1044982354889 / 1000000000000) (205175351 / 62500000) (820727313 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1407 / 64000) (11 / 500) (205175351 / 62500000) (820727313 / 250000000) (26407171 / 500000000000) (52830767 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (205175351 / 62500000) (820727313 / 250000000) (115664367 / 62500000) (370133167 / 200000000) (26407171 / 500000000000) (52830767 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0159 :
    ∀ t ∈ Set.Icc ((11 / 500) : ℝ) (1409 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((130622794361 / 125000000000) : ℝ) ≤ Real.exp (2 * (11 / 500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (11 / 500)) (130622794361 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1409 / 64000) : ℝ)) ≤ (522507505549 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1409 / 64000)) (522507505549 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1850665471 / 1000000000) : ℝ) ≤ Real.exp (3 * (1641454103 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1641454103 / 500000000) / 16) (1850665471 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((820752961 / 250000000) : ℝ) / 16) ≤ (370140287 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (820752961 / 250000000) / 16) (370140287 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((11 / 500) : ℝ) (1409 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1641454103 / 500000000) (820752961 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (11 / 500) (1409 / 64000) (130622794361 / 125000000000) (522507505549 / 500000000000) (1641454103 / 500000000) (820752961 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (11 / 500) (1409 / 64000) (1641454103 / 500000000) (820752961 / 250000000) (5279809 / 100000000000) (52814509 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1641454103 / 500000000) (820752961 / 250000000) (1850665471 / 1000000000) (370140287 / 200000000) (5279809 / 100000000000) (52814509 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch007 :
    ∀ t ∈ Set.Icc ((1389 / 64000) : ℝ) (1409 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0140
      hpThetaDensityTwoTermCompact_cell0141)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0142
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0143
      hpThetaDensityTwoTermCompact_cell0144)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0145
      hpThetaDensityTwoTermCompact_cell0146)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0147
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0148
      hpThetaDensityTwoTermCompact_cell0149))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0150
      hpThetaDensityTwoTermCompact_cell0151)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0152
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0153
      hpThetaDensityTwoTermCompact_cell0154)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0155
      hpThetaDensityTwoTermCompact_cell0156)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0157
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0158
      hpThetaDensityTwoTermCompact_cell0159)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch007
end HodgeProofHP
