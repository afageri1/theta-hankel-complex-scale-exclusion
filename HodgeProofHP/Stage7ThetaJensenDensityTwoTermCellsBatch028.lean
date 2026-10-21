/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0560 :
    ∀ t ∈ Set.Icc ((393 / 12800) : ℝ) (1967 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((66458175287 / 62500000000) : ℝ) ≤ Real.exp (2 * (393 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (393 / 12800)) (66458175287 / 62500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1967 / 64000) : ℝ)) ≤ (531698632423 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1967 / 64000)) (531698632423 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((935388091 / 500000000) : ℝ) ≤ Real.exp (3 * (3340551549 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3340551549 / 1000000000) / 16) (935388091 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((835190351 / 250000000) : ℝ) / 16) ≤ (374169959 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (835190351 / 250000000) / 16) (374169959 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((393 / 12800) : ℝ) (1967 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3340551549 / 1000000000) (835190351 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (393 / 12800) (1967 / 64000) (66458175287 / 62500000000) (531698632423 / 500000000000) (3340551549 / 1000000000) (835190351 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (393 / 12800) (1967 / 64000) (3340551549 / 1000000000) (835190351 / 250000000) (44399417 / 1000000000000) (44427379 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3340551549 / 1000000000) (835190351 / 250000000) (935388091 / 500000000) (374169959 / 200000000) (44399417 / 1000000000000) (44427379 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0561 :
    ∀ t ∈ Set.Icc ((1967 / 64000) : ℝ) (1969 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((212679452969 / 200000000000) : ℝ) ≤ Real.exp (2 * (1967 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1967 / 64000)) (212679452969 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1969 / 64000) : ℝ)) ≤ (265865932313 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1969 / 64000)) (265865932313 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1870849421 / 1000000000) : ℝ) ≤ Real.exp (3 * (167038017 / 50000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (167038017 / 50000000) / 16) (1870849421 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((104405319 / 31250000) : ℝ) / 16) ≤ (935461521 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (104405319 / 31250000) / 16) (935461521 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1967 / 64000) : ℝ) (1969 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (167038017 / 50000000) (104405319 / 31250000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1967 / 64000) (1969 / 64000) (212679452969 / 200000000000) (265865932313 / 250000000000) (167038017 / 50000000) (104405319 / 31250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1967 / 64000) (1969 / 64000) (167038017 / 50000000) (104405319 / 31250000) (44371613 / 1000000000000) (1109989 / 25000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (167038017 / 50000000) (104405319 / 31250000) (1870849421 / 1000000000) (935461521 / 500000000) (44371613 / 1000000000000) (1109989 / 25000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0562 :
    ∀ t ∈ Set.Icc ((1969 / 64000) : ℝ) (1971 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1063463729251 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1969 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1969 / 64000)) (1063463729251 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1971 / 64000) : ℝ)) ≤ (265882549453 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1971 / 64000)) (265882549453 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1870922667 / 1000000000) : ℝ) ≤ Real.exp (3 * (417621143 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (417621143 / 125000000) / 16) (1870922667 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((133647161 / 40000000) : ℝ) / 16) ≤ (233874537 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (133647161 / 40000000) / 16) (233874537 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1969 / 64000) : ℝ) (1971 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (417621143 / 125000000) (133647161 / 40000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1969 / 64000) (1971 / 64000) (1063463729251 / 1000000000000) (265882549453 / 250000000000) (417621143 / 125000000) (133647161 / 40000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1969 / 64000) (1971 / 64000) (417621143 / 125000000) (133647161 / 40000000) (1773753 / 40000000000) (11092939 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (417621143 / 125000000) (133647161 / 40000000) (1870922667 / 1000000000) (233874537 / 125000000) (1773753 / 40000000000) (11092939 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0563 :
    ∀ t ∈ Set.Icc ((1971 / 64000) : ℝ) (1973 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1063530197811 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1971 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1971 / 64000)) (1063530197811 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1973 / 64000) : ℝ)) ≤ (531798335263 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1973 / 64000)) (531798335263 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1870995921 / 1000000000) : ℝ) ≤ Real.exp (3 * (3341177961 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3341177961 / 1000000000) / 16) (1870995921 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((668277571 / 200000000) : ℝ) / 16) ≤ (1871069557 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (668277571 / 200000000) / 16) (1871069557 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1971 / 64000) : ℝ) (1973 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3341177961 / 1000000000) (668277571 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1971 / 64000) (1973 / 64000) (1063530197811 / 1000000000000) (531798335263 / 500000000000) (3341177961 / 1000000000) (668277571 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1971 / 64000) (1973 / 64000) (3341177961 / 1000000000) (668277571 / 200000000) (44316053 / 1000000000000) (1385749 / 31250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3341177961 / 1000000000) (668277571 / 200000000) (1870995921 / 1000000000) (1871069557 / 1000000000) (44316053 / 1000000000000) (1385749 / 31250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0564 :
    ∀ t ∈ Set.Icc ((1973 / 64000) : ℝ) (79 / 2560), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((42543866821 / 40000000000) : ℝ) ≤ Real.exp (2 * (1973 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1973 / 64000)) (42543866821 / 40000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((79 / 2560) : ℝ)) ≤ (265915786849 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (79 / 2560)) (265915786849 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1871069183 / 1000000000) : ℝ) ≤ Real.exp (3 * (3341386791 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3341386791 / 1000000000) / 16) (1871069183 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3341596699 / 1000000000) : ℝ) / 16) ≤ (935571413 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3341596699 / 1000000000) / 16) (935571413 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1973 / 64000) : ℝ) (79 / 2560),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3341386791 / 1000000000) (3341596699 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1973 / 64000) (79 / 2560) (42543866821 / 40000000000) (265915786849 / 250000000000) (3341386791 / 1000000000) (3341596699 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1973 / 64000) (79 / 2560) (3341386791 / 1000000000) (3341596699 / 1000000000) (5536037 / 125000000000) (11079049 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3341386791 / 1000000000) (3341596699 / 1000000000) (1871069183 / 1000000000) (935571413 / 500000000) (5536037 / 125000000000) (11079049 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0565 :
    ∀ t ∈ Set.Icc ((79 / 2560) : ℝ) (1977 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((212732629479 / 200000000000) : ℝ) ≤ Real.exp (2 * (79 / 2560)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (79 / 2560)) (212732629479 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1977 / 64000) : ℝ)) ≤ (53186481421 / 50000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1977 / 64000)) (53186481421 / 50000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((467785613 / 250000000) : ℝ) ≤ Real.exp (3 * (1670797817 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1670797817 / 500000000) / 16) (467785613 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((668361111 / 200000000) : ℝ) / 16) ≤ (1871216103 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (668361111 / 200000000) / 16) (1871216103 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((79 / 2560) : ℝ) (1977 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1670797817 / 500000000) (668361111 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (79 / 2560) (1977 / 64000) (212732629479 / 200000000000) (53186481421 / 50000000000) (1670797817 / 500000000) (668361111 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (79 / 2560) (1977 / 64000) (1670797817 / 500000000) (668361111 / 200000000) (8852111 / 200000000000) (44288439 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1670797817 / 500000000) (668361111 / 200000000) (467785613 / 250000000) (1871216103 / 1000000000) (8852111 / 200000000000) (44288439 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0566 :
    ∀ t ∈ Set.Icc ((1977 / 64000) : ℝ) (1979 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1063729628419 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1977 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1977 / 64000)) (1063729628419 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1979 / 64000) : ℝ)) ≤ (1063796113599 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1979 / 64000)) (1063796113599 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((116950983 / 62500000) : ℝ) ≤ Real.exp (3 * (334180449 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (334180449 / 100000000) / 16) (116950983 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((417751803 / 125000000) : ℝ) / 16) ≤ (1871289387 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (417751803 / 125000000) / 16) (1871289387 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1977 / 64000) : ℝ) (1979 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (334180449 / 100000000) (417751803 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1977 / 64000) (1979 / 64000) (1063729628419 / 1000000000000) (1063796113599 / 1000000000000) (334180449 / 100000000) (417751803 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1977 / 64000) (1979 / 64000) (334180449 / 100000000) (417751803 / 125000000) (4423283 / 100000000000) (22130349 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (334180449 / 100000000) (417751803 / 125000000) (116950983 / 62500000) (1871289387 / 1000000000) (4423283 / 100000000000) (22130349 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0567 :
    ∀ t ∈ Set.Icc ((1979 / 64000) : ℝ) (1981 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((531898056799 / 500000000000) : ℝ) ≤ Real.exp (2 * (1979 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1979 / 64000)) (531898056799 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1981 / 64000) : ℝ)) ≤ (531931301467 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1981 / 64000)) (531931301467 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((467822253 / 250000000) : ℝ) ≤ Real.exp (3 * (41775167 / 12500000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (41775167 / 12500000) / 16) (467822253 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3342223307 / 1000000000) : ℝ) / 16) ≤ (935681339 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3342223307 / 1000000000) / 16) (935681339 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1979 / 64000) : ℝ) (1981 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (41775167 / 12500000) (3342223307 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1979 / 64000) (1981 / 64000) (531898056799 / 500000000000) (531931301467 / 500000000000) (41775167 / 12500000) (3342223307 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1979 / 64000) (1981 / 64000) (41775167 / 12500000) (3342223307 / 1000000000) (138141 / 3125000000) (44232973 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (41775167 / 12500000) (3342223307 / 1000000000) (467822253 / 250000000) (935681339 / 500000000) (138141 / 3125000000) (44232973 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0568 :
    ∀ t ∈ Set.Icc ((1981 / 64000) : ℝ) (1983 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1063862602933 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1981 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1981 / 64000)) (1063862602933 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1983 / 64000) : ℝ)) ≤ (42557163857 / 40000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1983 / 64000)) (42557163857 / 40000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1871362303 / 1000000000) : ℝ) ≤ Real.exp (3 * (1671111121 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1671111121 / 500000000) / 16) (1871362303 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1671216101 / 500000000) : ℝ) / 16) ≤ (1871435977 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1671216101 / 500000000) / 16) (1871435977 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1981 / 64000) : ℝ) (1983 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1671111121 / 500000000) (1671216101 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1981 / 64000) (1983 / 64000) (1063862602933 / 1000000000000) (42557163857 / 40000000000) (1671111121 / 500000000) (1671216101 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1981 / 64000) (1983 / 64000) (1671111121 / 500000000) (1671216101 / 500000000) (22088713 / 500000000000) (44205263 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1671111121 / 500000000) (1671216101 / 500000000) (1871362303 / 1000000000) (1871435977 / 1000000000) (22088713 / 500000000000) (44205263 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0569 :
    ∀ t ∈ Set.Icc ((1983 / 64000) : ℝ) (397 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((132991137053 / 125000000000) : ℝ) ≤ Real.exp (2 * (1983 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1983 / 64000)) (132991137053 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((397 / 12800) : ℝ)) ≤ (1063995594071 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (397 / 12800)) (1063995594071 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((935717801 / 500000000) : ℝ) ≤ Real.exp (3 * (3342431137 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3342431137 / 1000000000) / 16) (935717801 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3342641111 / 1000000000) : ℝ) / 16) ≤ (1871509283 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3342641111 / 1000000000) / 16) (1871509283 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1983 / 64000) : ℝ) (397 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3342431137 / 1000000000) (3342641111 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1983 / 64000) (397 / 12800) (132991137053 / 125000000000) (1063995594071 / 1000000000000) (3342431137 / 1000000000) (3342641111 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1983 / 64000) (397 / 12800) (3342431137 / 1000000000) (3342641111 / 1000000000) (11037437 / 250000000000) (44177569 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3342431137 / 1000000000) (3342641111 / 1000000000) (935717801 / 500000000) (1871509283 / 1000000000) (11037437 / 250000000000) (44177569 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0570 :
    ∀ t ∈ Set.Icc ((397 / 12800) : ℝ) (1987 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((106399559407 / 100000000000) : ℝ) ≤ Real.exp (2 * (397 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (397 / 12800)) (106399559407 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1987 / 64000) : ℝ)) ≤ (532031047937 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1987 / 64000)) (532031047937 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((467877227 / 250000000) : ℝ) ≤ Real.exp (3 * (1671320023 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1671320023 / 500000000) / 16) (467877227 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((208928127 / 62500000) : ℝ) / 16) ≤ (1871582597 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (208928127 / 62500000) / 16) (1871582597 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((397 / 12800) : ℝ) (1987 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1671320023 / 500000000) (208928127 / 62500000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (397 / 12800) (1987 / 64000) (106399559407 / 100000000000) (532031047937 / 500000000000) (1671320023 / 500000000) (208928127 / 62500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (397 / 12800) (1987 / 64000) (1671320023 / 500000000) (208928127 / 62500000) (8824417 / 200000000000) (4414989 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1671320023 / 500000000) (208928127 / 62500000) (467877227 / 250000000) (1871582597 / 1000000000) (8824417 / 200000000000) (4414989 / 100000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0571 :
    ∀ t ∈ Set.Icc ((1987 / 64000) : ℝ) (1989 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1064062095873 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1987 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1987 / 64000)) (1064062095873 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1989 / 64000) : ℝ)) ≤ (1064128601833 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1989 / 64000)) (1064128601833 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((935791111 / 500000000) : ℝ) ≤ Real.exp (3 * (3342848967 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3342848967 / 1000000000) / 16) (935791111 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3343058967 / 1000000000) : ℝ) / 16) ≤ (935827959 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3343058967 / 1000000000) / 16) (935827959 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1987 / 64000) : ℝ) (1989 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3342848967 / 1000000000) (3343058967 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1987 / 64000) (1989 / 64000) (1064062095873 / 1000000000000) (1064128601833 / 1000000000000) (3342848967 / 1000000000) (3343058967 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1987 / 64000) (1989 / 64000) (3342848967 / 1000000000) (3343058967 / 1000000000) (44094437 / 1000000000000) (44122227 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3342848967 / 1000000000) (3343058967 / 1000000000) (935791111 / 500000000) (935827959 / 500000000) (44094437 / 1000000000000) (44122227 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0572 :
    ∀ t ∈ Set.Icc ((1989 / 64000) : ℝ) (1991 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((133016075229 / 125000000000) : ℝ) ≤ Real.exp (2 * (1989 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1989 / 64000)) (133016075229 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1991 / 64000) : ℝ)) ≤ (1064195111949 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1991 / 64000)) (1064195111949 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1871655543 / 1000000000) : ℝ) ≤ Real.exp (3 * (1671528951 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1671528951 / 500000000) / 16) (1871655543 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((668653583 / 200000000) : ℝ) / 16) ≤ (1871729247 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (668653583 / 200000000) / 16) (1871729247 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1989 / 64000) : ℝ) (1991 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1671528951 / 500000000) (668653583 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1989 / 64000) (1991 / 64000) (133016075229 / 125000000000) (1064195111949 / 1000000000000) (1671528951 / 500000000) (668653583 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1989 / 64000) (1991 / 64000) (1671528951 / 500000000) (668653583 / 200000000) (22033403 / 500000000000) (2204729 / 50000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1671528951 / 500000000) (668653583 / 200000000) (1871655543 / 1000000000) (1871729247 / 1000000000) (22033403 / 500000000000) (2204729 / 50000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0573 :
    ∀ t ∈ Set.Icc ((1991 / 64000) : ℝ) (1993 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((266048777987 / 250000000000) : ℝ) ≤ Real.exp (2 * (1991 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1991 / 64000)) (266048777987 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1993 / 64000) : ℝ)) ≤ (532130813111 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1993 / 64000)) (532130813111 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((233966109 / 125000000) : ℝ) ≤ Real.exp (3 * (66865337 / 20000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (66865337 / 20000000) / 16) (233966109 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((835869219 / 250000000) : ℝ) / 16) ≤ (1871802583 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (835869219 / 250000000) / 16) (1871802583 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1991 / 64000) : ℝ) (1993 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (66865337 / 20000000) (835869219 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1991 / 64000) (1993 / 64000) (266048777987 / 250000000000) (532130813111 / 500000000000) (66865337 / 20000000) (835869219 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1991 / 64000) (1993 / 64000) (66865337 / 20000000) (835869219 / 250000000) (4403919 / 100000000000) (11016737 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (66865337 / 20000000) (835869219 / 250000000) (233966109 / 125000000) (1871802583 / 1000000000) (4403919 / 100000000000) (11016737 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0574 :
    ∀ t ∈ Set.Icc ((1993 / 64000) : ℝ) (399 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1064261626221 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1993 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1993 / 64000)) (1064261626221 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((399 / 12800) : ℝ)) ≤ (1064328144653 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (399 / 12800)) (1064328144653 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((58493819 / 31250000) : ℝ) ≤ Real.exp (3 * (334347581 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (334347581 / 100000000) / 16) (58493819 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3343685849 / 1000000000) : ℝ) / 16) ≤ (935937963 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3343685849 / 1000000000) / 16) (935937963 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1993 / 64000) : ℝ) (399 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (334347581 / 100000000) (3343685849 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1993 / 64000) (399 / 12800) (1064261626221 / 1000000000000) (1064328144653 / 1000000000000) (334347581 / 100000000) (3343685849 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1993 / 64000) (399 / 12800) (334347581 / 100000000) (3343685849 / 1000000000) (44011589 / 1000000000000) (11009833 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (334347581 / 100000000) (3343685849 / 1000000000) (58493819 / 31250000) (935937963 / 500000000) (44011589 / 1000000000000) (11009833 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0575 :
    ∀ t ∈ Set.Icc ((399 / 12800) : ℝ) (1997 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((266082036163 / 250000000000) : ℝ) ≤ Real.exp (2 * (399 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (399 / 12800)) (266082036163 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1997 / 64000) : ℝ)) ≤ (1064394667241 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1997 / 64000)) (1064394667241 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1871875551 / 1000000000) : ℝ) ≤ Real.exp (3 * (208980299 / 62500000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (208980299 / 62500000) / 16) (1871875551 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((835973709 / 250000000) : ℝ) / 16) ≤ (1871949277 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (835973709 / 250000000) / 16) (1871949277 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((399 / 12800) : ℝ) (1997 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (208980299 / 62500000) (835973709 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (399 / 12800) (1997 / 64000) (266082036163 / 250000000000) (1064394667241 / 1000000000000) (208980299 / 62500000) (835973709 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (399 / 12800) (1997 / 64000) (208980299 / 62500000) (835973709 / 250000000) (10996001 / 250000000000) (44011731 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (208980299 / 62500000) (835973709 / 250000000) (1871875551 / 1000000000) (1871949277 / 1000000000) (10996001 / 250000000000) (44011731 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0576 :
    ∀ t ∈ Set.Icc ((1997 / 64000) : ℝ) (1999 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((26609866681 / 25000000000) : ℝ) ≤ Real.exp (2 * (1997 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1997 / 64000)) (26609866681 / 25000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1999 / 64000) : ℝ)) ≤ (532230596993 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1999 / 64000)) (532230596993 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((935974451 / 500000000) : ℝ) ≤ Real.exp (3 * (3343893771 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3343893771 / 1000000000) / 16) (935974451 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((836025959 / 250000000) : ℝ) / 16) ≤ (374404527 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (836025959 / 250000000) / 16) (374404527 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1997 / 64000) : ℝ) (1999 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3343893771 / 1000000000) (836025959 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1997 / 64000) (1999 / 64000) (26609866681 / 25000000000) (532230596993 / 500000000000) (3343893771 / 1000000000) (836025959 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1997 / 64000) (1999 / 64000) (3343893771 / 1000000000) (836025959 / 250000000) (8791287 / 200000000000) (21992073 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3343893771 / 1000000000) (836025959 / 250000000) (935974451 / 500000000) (374404527 / 200000000) (8791287 / 200000000000) (21992073 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0577 :
    ∀ t ∈ Set.Icc ((1999 / 64000) : ℝ) (2001 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((212892238797 / 200000000000) : ℝ) ≤ Real.exp (2 * (1999 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1999 / 64000)) (212892238797 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2001 / 64000) : ℝ)) ≤ (106452772489 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2001 / 64000)) (106452772489 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1872022261 / 1000000000) : ℝ) ≤ Real.exp (3 * (3344102771 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3344102771 / 1000000000) / 16) (1872022261 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3344312849 / 1000000000) : ℝ) / 16) ≤ (1872096001 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3344312849 / 1000000000) / 16) (1872096001 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1999 / 64000) : ℝ) (2001 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3344102771 / 1000000000) (3344312849 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1999 / 64000) (2001 / 64000) (212892238797 / 200000000000) (106452772489 / 100000000000) (3344102771 / 1000000000) (3344312849 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1999 / 64000) (2001 / 64000) (3344102771 / 1000000000) (3344312849 / 1000000000) (21964441 / 500000000000) (43956577 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3344102771 / 1000000000) (3344312849 / 1000000000) (1872022261 / 1000000000) (1872096001 / 1000000000) (21964441 / 500000000000) (43956577 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0578 :
    ∀ t ∈ Set.Icc ((2001 / 64000) : ℝ) (2003 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1064527724889 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2001 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2001 / 64000)) (1064527724889 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2003 / 64000) : ℝ)) ≤ (66537141247 / 62500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2003 / 64000)) (66537141247 / 62500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((936047813 / 500000000) : ℝ) ≤ Real.exp (3 * (418038973 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (418038973 / 125000000) / 16) (936047813 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1070247 / 320000) : ℝ) / 16) ≤ (2995471 / 1600000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1070247 / 320000) / 16) (2995471 / 1600000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2001 / 64000) : ℝ) (2003 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (418038973 / 125000000) (1070247 / 320000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2001 / 64000) (2003 / 64000) (1064527724889 / 1000000000000) (66537141247 / 62500000000) (418038973 / 125000000) (1070247 / 320000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2001 / 64000) (2003 / 64000) (418038973 / 125000000) (1070247 / 320000) (43901343 / 1000000000000) (43929023 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (418038973 / 125000000) (1070247 / 320000) (936047813 / 500000000) (2995471 / 1600000) (43901343 / 1000000000000) (43929023 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0579 :
    ∀ t ∈ Set.Icc ((2003 / 64000) : ℝ) (401 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1064594259951 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2003 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2003 / 64000)) (1064594259951 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((401 / 12800) : ℝ)) ≤ (1064660799173 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (401 / 12800)) (1064660799173 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1872169 / 1000000) : ℝ) ≤ Real.exp (3 * (334452081 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (334452081 / 100000000) / 16) (1872169 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((668946183 / 200000000) : ℝ) / 16) ≤ (468060689 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (668946183 / 200000000) / 16) (468060689 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2003 / 64000) : ℝ) (401 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (334452081 / 100000000) (668946183 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2003 / 64000) (401 / 12800) (1064594259951 / 1000000000000) (1064660799173 / 1000000000000) (334452081 / 100000000) (668946183 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2003 / 64000) (401 / 12800) (334452081 / 100000000) (668946183 / 200000000) (2193691 / 50000000000) (8780297 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (334452081 / 100000000) (668946183 / 200000000) (1872169 / 1000000) (468060689 / 250000000) (2193691 / 50000000000) (8780297 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch028 :
    ∀ t ∈ Set.Icc ((393 / 12800) : ℝ) (401 / 12800),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0560
      hpThetaDensityTwoTermCompact_cell0561)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0562
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0563
      hpThetaDensityTwoTermCompact_cell0564)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0565
      hpThetaDensityTwoTermCompact_cell0566)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0567
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0568
      hpThetaDensityTwoTermCompact_cell0569))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0570
      hpThetaDensityTwoTermCompact_cell0571)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0572
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0573
      hpThetaDensityTwoTermCompact_cell0574)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0575
      hpThetaDensityTwoTermCompact_cell0576)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0577
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0578
      hpThetaDensityTwoTermCompact_cell0579)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch028
end HodgeProofHP
