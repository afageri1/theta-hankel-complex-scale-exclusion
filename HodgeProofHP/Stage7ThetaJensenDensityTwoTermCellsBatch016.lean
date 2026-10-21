/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0320 :
    ∀ t ∈ Set.Icc ((1569 / 64000) : ℝ) (157 / 6400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((525126585319 / 500000000000) : ℝ) ≤ Real.exp (2 * (1569 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1569 / 64000)) (525126585319 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((157 / 6400) : ℝ)) ≤ (262571497891 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (157 / 6400)) (262571497891 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1856420283 / 1000000000) : ℝ) ≤ Real.exp (3 * (1649733479 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1649733479 / 500000000) / 16) (1856420283 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((41244639 / 12500000) : ℝ) / 16) ≤ (1856456541 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (41244639 / 12500000) / 16) (1856456541 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1569 / 64000) : ℝ) (157 / 6400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1649733479 / 500000000) (41244639 / 12500000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1569 / 64000) (157 / 6400) (525126585319 / 500000000000) (262571497891 / 250000000000) (1649733479 / 500000000) (41244639 / 12500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1569 / 64000) (157 / 6400) (1649733479 / 500000000) (41244639 / 12500000) (627991 / 12500000000) (50254983 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1649733479 / 500000000) (41244639 / 12500000) (1856420283 / 1000000000) (1856456541 / 1000000000) (627991 / 12500000000) (50254983 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0321 :
    ∀ t ∈ Set.Icc ((157 / 6400) : ℝ) (1571 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1050285991563 / 1000000000000) : ℝ) ≤ Real.exp (2 * (157 / 6400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (157 / 6400)) (1050285991563 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1571 / 64000) : ℝ)) ≤ (525159406757 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1571 / 64000)) (525159406757 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((928228087 / 500000000) : ℝ) ≤ Real.exp (3 * (824892517 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (824892517 / 250000000) / 16) (928228087 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3299674233 / 1000000000) : ℝ) / 16) ≤ (928246217 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3299674233 / 1000000000) / 16) (928246217 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((157 / 6400) : ℝ) (1571 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (824892517 / 250000000) (3299674233 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (157 / 6400) (1571 / 64000) (1050285991563 / 1000000000000) (525159406757 / 500000000000) (824892517 / 250000000) (3299674233 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (157 / 6400) (1571 / 64000) (824892517 / 250000000) (3299674233 / 1000000000) (50223741 / 1000000000000) (627993 / 12500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (824892517 / 250000000) (3299674233 / 1000000000) (928228087 / 500000000) (928246217 / 500000000) (50223741 / 1000000000000) (627993 / 12500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0322 :
    ∀ t ∈ Set.Icc ((1571 / 64000) : ℝ) (393 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1050318813513 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1571 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1571 / 64000)) (1050318813513 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((393 / 16000) : ℝ)) ≤ (105035163649 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (393 / 16000)) (105035163649 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((928246033 / 500000000) : ℝ) ≤ Real.exp (3 * (3299673181 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3299673181 / 1000000000) / 16) (928246033 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3299777349 / 1000000000) : ℝ) / 16) ≤ (232066041 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3299777349 / 1000000000) / 16) (232066041 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1571 / 64000) : ℝ) (393 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3299673181 / 1000000000) (3299777349 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1571 / 64000) (393 / 16000) (1050318813513 / 1000000000000) (105035163649 / 100000000000) (3299673181 / 1000000000) (3299777349 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1571 / 64000) (393 / 16000) (3299673181 / 1000000000) (3299777349 / 1000000000) (50208207 / 1000000000000) (50223901 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3299673181 / 1000000000) (3299777349 / 1000000000) (928246033 / 500000000) (232066041 / 125000000) (50208207 / 1000000000000) (50223901 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0323 :
    ∀ t ∈ Set.Icc ((393 / 16000) : ℝ) (1573 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1050351636489 / 1000000000000) : ℝ) ≤ Real.exp (2 * (393 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (393 / 16000)) (1050351636489 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1573 / 64000) : ℝ)) ≤ (1050384460491 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1573 / 64000)) (1050384460491 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1856527961 / 1000000000) : ℝ) ≤ Real.exp (3 * (1649888149 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1649888149 / 500000000) / 16) (1856527961 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3299880469 / 1000000000) : ℝ) / 16) ≤ (3626102 / 1953125) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3299880469 / 1000000000) / 16) (3626102 / 1953125) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((393 / 16000) : ℝ) (1573 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1649888149 / 500000000) (3299880469 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (393 / 16000) (1573 / 64000) (1050351636489 / 1000000000000) (1050384460491 / 1000000000000) (1649888149 / 500000000) (3299880469 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (393 / 16000) (1573 / 64000) (1649888149 / 500000000) (3299880469 / 1000000000) (50192677 / 1000000000000) (50208367 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1649888149 / 500000000) (3299880469 / 1000000000) (1856527961 / 1000000000) (3626102 / 1953125) (50192677 / 1000000000000) (50208367 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0324 :
    ∀ t ∈ Set.Icc ((1573 / 64000) : ℝ) (787 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((105038446049 / 100000000000) : ℝ) ≤ Real.exp (2 * (1573 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1573 / 64000)) (105038446049 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((787 / 32000) : ℝ)) ≤ (525208642759 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (787 / 32000)) (525208642759 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1856563857 / 1000000000) : ℝ) ≤ Real.exp (3 * (3299879417 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3299879417 / 1000000000) / 16) (1856563857 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((412497949 / 125000000) : ℝ) / 16) ≤ (928300061 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (412497949 / 125000000) / 16) (928300061 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1573 / 64000) : ℝ) (787 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3299879417 / 1000000000) (412497949 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1573 / 64000) (787 / 32000) (105038446049 / 100000000000) (525208642759 / 500000000000) (3299879417 / 1000000000) (412497949 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1573 / 64000) (787 / 32000) (3299879417 / 1000000000) (412497949 / 125000000) (50177151 / 1000000000000) (50192837 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3299879417 / 1000000000) (412497949 / 125000000) (1856563857 / 1000000000) (928300061 / 500000000) (50177151 / 1000000000000) (50192837 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0325 :
    ∀ t ∈ Set.Icc ((787 / 32000) : ℝ) (63 / 2560), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1050417285517 / 1000000000000) : ℝ) ≤ Real.exp (2 * (787 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (787 / 32000)) (1050417285517 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((63 / 2560) : ℝ)) ≤ (1050450111571 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (63 / 2560)) (1050450111571 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((371319951 / 200000000) : ℝ) ≤ Real.exp (3 * (164999127 / 50000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (164999127 / 50000000) / 16) (371319951 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1650043359 / 500000000) : ℝ) / 16) ≤ (928318011 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1650043359 / 500000000) / 16) (928318011 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((787 / 32000) : ℝ) (63 / 2560),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (164999127 / 50000000) (1650043359 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (787 / 32000) (63 / 2560) (1050417285517 / 1000000000000) (1050450111571 / 1000000000000) (164999127 / 50000000) (1650043359 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (787 / 32000) (63 / 2560) (164999127 / 50000000) (1650043359 / 500000000) (5016163 / 100000000000) (50177311 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (164999127 / 50000000) (1650043359 / 500000000) (371319951 / 200000000) (928318011 / 500000000) (5016163 / 100000000000) (50177311 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0326 :
    ∀ t ∈ Set.Icc ((63 / 2560) : ℝ) (197 / 8000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((105045011157 / 100000000000) : ℝ) ≤ Real.exp (2 * (63 / 2560)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (63 / 2560)) (105045011157 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((197 / 8000) : ℝ)) ≤ (21009658773 / 20000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (197 / 8000)) (21009658773 / 20000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((371327131 / 200000000) : ℝ) ≤ Real.exp (3 * (1650042833 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1650042833 / 500000000) / 16) (371327131 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3300189847 / 1000000000) : ℝ) / 16) ≤ (1856671923 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3300189847 / 1000000000) / 16) (1856671923 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((63 / 2560) : ℝ) (197 / 8000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1650042833 / 500000000) (3300189847 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (63 / 2560) (197 / 8000) (105045011157 / 100000000000) (21009658773 / 20000000000) (1650042833 / 500000000) (3300189847 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (63 / 2560) (197 / 8000) (1650042833 / 500000000) (3300189847 / 1000000000) (50146113 / 1000000000000) (5016179 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1650042833 / 500000000) (3300189847 / 1000000000) (371327131 / 200000000) (1856671923 / 1000000000) (50146113 / 1000000000000) (5016179 / 100000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0327 :
    ∀ t ∈ Set.Icc ((197 / 8000) : ℝ) (1577 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1050482938649 / 1000000000000) : ℝ) ≤ Real.exp (2 * (197 / 8000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (197 / 8000)) (1050482938649 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1577 / 64000) : ℝ)) ≤ (210103153351 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1577 / 64000)) (210103153351 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1856671557 / 1000000000) : ℝ) ≤ Real.exp (3 * (825047199 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (825047199 / 250000000) / 16) (1856671557 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((165014649 / 50000000) : ℝ) / 16) ≤ (1856707827 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (165014649 / 50000000) / 16) (1856707827 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((197 / 8000) : ℝ) (1577 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (825047199 / 250000000) (165014649 / 50000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (197 / 8000) (1577 / 64000) (1050482938649 / 1000000000000) (210103153351 / 200000000000) (825047199 / 250000000) (165014649 / 50000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (197 / 8000) (1577 / 64000) (825047199 / 250000000) (165014649 / 50000000) (250653 / 5000000000) (1567071 / 31250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (825047199 / 250000000) (165014649 / 50000000) (1856671557 / 1000000000) (1856707827 / 1000000000) (250653 / 5000000000) (1567071 / 31250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0328 :
    ∀ t ∈ Set.Icc ((1577 / 64000) : ℝ) (789 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((525257883377 / 500000000000) : ℝ) ≤ Real.exp (2 * (1577 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1577 / 64000)) (525257883377 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((789 / 32000) : ℝ)) ≤ (525274297943 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (789 / 32000)) (525274297943 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((92835373 / 50000000) : ℝ) ≤ Real.exp (3 * (412536491 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (412536491 / 125000000) / 16) (92835373 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((660079223 / 200000000) : ℝ) / 16) ≤ (464185933 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (660079223 / 200000000) / 16) (464185933 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1577 / 64000) : ℝ) (789 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (412536491 / 125000000) (660079223 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1577 / 64000) (789 / 32000) (525257883377 / 500000000000) (525274297943 / 500000000000) (412536491 / 125000000) (660079223 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1577 / 64000) (789 / 32000) (412536491 / 125000000) (660079223 / 200000000) (12528773 / 250000000000) (1253269 / 25000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (412536491 / 125000000) (660079223 / 200000000) (92835373 / 50000000) (464185933 / 250000000) (12528773 / 250000000000) (1253269 / 25000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0329 :
    ∀ t ∈ Set.Icc ((789 / 32000) : ℝ) (1579 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((210109719177 / 200000000000) : ℝ) ≤ Real.exp (2 * (789 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (789 / 32000)) (210109719177 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1579 / 64000) : ℝ)) ≤ (525290713021 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1579 / 64000)) (525290713021 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((371348673 / 200000000) : ℝ) ≤ Real.exp (3 * (412549383 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (412549383 / 125000000) / 16) (371348673 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1650249627 / 500000000) : ℝ) / 16) ≤ (1856779639 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1650249627 / 500000000) / 16) (1856779639 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((789 / 32000) : ℝ) (1579 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (412549383 / 125000000) (1650249627 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (789 / 32000) (1579 / 64000) (210109719177 / 200000000000) (525290713021 / 500000000000) (412549383 / 125000000) (1650249627 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (789 / 32000) (1579 / 64000) (412549383 / 125000000) (1650249627 / 500000000) (12524897 / 250000000000) (50115251 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (412549383 / 125000000) (1650249627 / 500000000) (371348673 / 200000000) (1856779639 / 1000000000) (12524897 / 250000000000) (50115251 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0330 :
    ∀ t ∈ Set.Icc ((1579 / 64000) : ℝ) (79 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1050581426041 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1579 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1579 / 64000)) (1050581426041 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((79 / 3200) : ℝ)) ≤ (42024570289 / 40000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (79 / 3200)) (42024570289 / 40000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((232097409 / 125000000) : ℝ) ≤ Real.exp (3 * (3300498203 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3300498203 / 1000000000) / 16) (232097409 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3300602397 / 1000000000) : ℝ) / 16) ≤ (464203887 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3300602397 / 1000000000) / 16) (464203887 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1579 / 64000) : ℝ) (79 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3300498203 / 1000000000) (3300602397 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1579 / 64000) (79 / 3200) (1050581426041 / 1000000000000) (42024570289 / 40000000000) (3300498203 / 1000000000) (3300602397 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1579 / 64000) (79 / 3200) (3300498203 / 1000000000) (3300602397 / 1000000000) (6260511 / 125000000000) (50099747 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3300498203 / 1000000000) (3300602397 / 1000000000) (232097409 / 125000000) (464203887 / 250000000) (6260511 / 125000000000) (50099747 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0331 :
    ∀ t ∈ Set.Icc ((79 / 3200) : ℝ) (1581 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((131326782153 / 125000000000) : ℝ) ≤ Real.exp (2 * (79 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (79 / 3200)) (131326782153 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1581 / 64000) : ℝ)) ≤ (1050647089433 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1581 / 64000)) (1050647089433 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1856815181 / 1000000000) : ℝ) ≤ Real.exp (3 * (660120269 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (660120269 / 200000000) / 16) (1856815181 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1650352771 / 500000000) : ℝ) / 16) ≤ (1856851459 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1650352771 / 500000000) / 16) (1856851459 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((79 / 3200) : ℝ) (1581 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (660120269 / 200000000) (1650352771 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (79 / 3200) (1581 / 64000) (131326782153 / 125000000000) (1050647089433 / 1000000000000) (660120269 / 200000000) (1650352771 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (79 / 3200) (1581 / 64000) (660120269 / 200000000) (1650352771 / 500000000) (50068593 / 1000000000000) (6260531 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (660120269 / 200000000) (1650352771 / 500000000) (1856815181 / 1000000000) (1856851459 / 1000000000) (50068593 / 1000000000000) (6260531 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0332 :
    ∀ t ∈ Set.Icc ((1581 / 64000) : ℝ) (791 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((131330886179 / 125000000000) : ℝ) ≤ Real.exp (2 * (1581 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1581 / 64000)) (131330886179 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((791 / 32000) : ℝ)) ≤ (262669980667 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (791 / 32000)) (262669980667 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((464212773 / 250000000) : ℝ) ≤ Real.exp (3 * (330070449 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (330070449 / 100000000) / 16) (464212773 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3300808691 / 1000000000) : ℝ) / 16) ≤ (464221843 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3300808691 / 1000000000) / 16) (464221843 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1581 / 64000) : ℝ) (791 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (330070449 / 100000000) (3300808691 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1581 / 64000) (791 / 32000) (131330886179 / 125000000000) (262669980667 / 250000000000) (330070449 / 100000000) (3300808691 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1581 / 64000) (791 / 32000) (330070449 / 100000000) (3300808691 / 1000000000) (50053101 / 1000000000000) (3129297 / 62500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (330070449 / 100000000) (3300808691 / 1000000000) (464212773 / 250000000) (464221843 / 250000000) (50053101 / 1000000000000) (3129297 / 62500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0333 :
    ∀ t ∈ Set.Icc ((791 / 32000) : ℝ) (1583 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1050679922667 / 1000000000000) : ℝ) ≤ Real.exp (2 * (791 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (791 / 32000)) (1050679922667 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1583 / 64000) : ℝ)) ≤ (1050712756929 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1583 / 64000)) (1050712756929 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((464221751 / 250000000) : ℝ) ≤ Real.exp (3 * (3300807639 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3300807639 / 1000000000) / 16) (464221751 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3300911843 / 1000000000) : ℝ) / 16) ≤ (928461643 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3300911843 / 1000000000) / 16) (928461643 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((791 / 32000) : ℝ) (1583 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3300807639 / 1000000000) (3300911843 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (791 / 32000) (1583 / 64000) (1050679922667 / 1000000000000) (1050712756929 / 1000000000000) (3300807639 / 1000000000) (3300911843 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (791 / 32000) (1583 / 64000) (3300807639 / 1000000000) (3300911843 / 1000000000) (10007523 / 200000000000) (50053261 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3300807639 / 1000000000) (3300911843 / 1000000000) (464221751 / 250000000) (928461643 / 500000000) (10007523 / 200000000000) (50053261 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0334 :
    ∀ t ∈ Set.Icc ((1583 / 64000) : ℝ) (99 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((16417386827 / 15625000000) : ℝ) ≤ Real.exp (2 * (1583 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1583 / 64000)) (16417386827 / 15625000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((99 / 4000) : ℝ)) ≤ (210149118443 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (99 / 4000)) (210149118443 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1856922919 / 1000000000) : ℝ) ≤ Real.exp (3 * (3300910791 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3300910791 / 1000000000) / 16) (1856922919 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1650507499 / 500000000) : ℝ) / 16) ≤ (928479601 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1650507499 / 500000000) / 16) (928479601 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1583 / 64000) : ℝ) (99 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3300910791 / 1000000000) (1650507499 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1583 / 64000) (99 / 4000) (16417386827 / 15625000000) (210149118443 / 200000000000) (3300910791 / 1000000000) (1650507499 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1583 / 64000) (99 / 4000) (3300910791 / 1000000000) (1650507499 / 500000000) (12505533 / 250000000000) (25018887 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3300910791 / 1000000000) (1650507499 / 500000000) (1856922919 / 1000000000) (928479601 / 500000000) (12505533 / 250000000000) (25018887 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0335 :
    ∀ t ∈ Set.Icc ((99 / 4000) : ℝ) (317 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((525372796107 / 500000000000) : ℝ) ≤ Real.exp (2 * (99 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (99 / 4000)) (525372796107 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((317 / 12800) : ℝ)) ≤ (65673651783 / 62500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (317 / 12800)) (65673651783 / 62500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((371391767 / 200000000) : ℝ) ≤ Real.exp (3 * (1650506973 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1650506973 / 500000000) / 16) (371391767 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((825279539 / 250000000) : ℝ) / 16) ≤ (23212439 / 12500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (825279539 / 250000000) / 16) (23212439 / 12500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((99 / 4000) : ℝ) (317 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1650506973 / 500000000) (825279539 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (99 / 4000) (317 / 12800) (525372796107 / 500000000000) (65673651783 / 62500000000) (1650506973 / 500000000) (825279539 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (99 / 4000) (317 / 12800) (1650506973 / 500000000) (825279539 / 250000000) (25003327 / 500000000000) (50022291 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1650506973 / 500000000) (825279539 / 250000000) (371391767 / 200000000) (23212439 / 12500000) (25003327 / 500000000000) (50022291 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0336 :
    ∀ t ∈ Set.Icc ((317 / 12800) : ℝ) (793 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1050778428527 / 1000000000000) : ℝ) ≤ Real.exp (2 * (317 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (317 / 12800)) (1050778428527 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((793 / 32000) : ℝ)) ≤ (1050811265867 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (793 / 32000)) (1050811265867 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1856994753 / 1000000000) : ℝ) ≤ Real.exp (3 * (206319819 / 62500000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (206319819 / 62500000) / 16) (1856994753 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1650610659 / 500000000) : ℝ) / 16) ≤ (2901611 / 1562500) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1650610659 / 500000000) / 16) (2901611 / 1562500) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((317 / 12800) : ℝ) (793 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (206319819 / 62500000) (1650610659 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (317 / 12800) (793 / 32000) (1050778428527 / 1000000000000) (1050811265867 / 1000000000000) (206319819 / 62500000) (1650610659 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (317 / 12800) (793 / 32000) (206319819 / 62500000) (1650610659 / 500000000) (2499559 / 50000000000) (50006813 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (206319819 / 62500000) (1650610659 / 500000000) (1856994753 / 1000000000) (2901611 / 1562500) (2499559 / 50000000000) (50006813 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0337 :
    ∀ t ∈ Set.Icc ((793 / 32000) : ℝ) (1587 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((525405632933 / 500000000000) : ℝ) ≤ Real.exp (2 * (793 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (793 / 32000)) (525405632933 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1587 / 64000) : ℝ)) ≤ (131355513029 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1587 / 64000)) (131355513029 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1857030673 / 1000000000) : ℝ) ≤ Real.exp (3 * (1650610133 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1650610133 / 500000000) / 16) (1857030673 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1650662241 / 500000000) : ℝ) / 16) ≤ (1857066961 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1650662241 / 500000000) / 16) (1857066961 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((793 / 32000) : ℝ) (1587 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1650610133 / 500000000) (1650662241 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (793 / 32000) (1587 / 64000) (525405632933 / 500000000000) (131355513029 / 125000000000) (1650610133 / 500000000) (1650662241 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (793 / 32000) (1587 / 64000) (1650610133 / 500000000) (1650662241 / 500000000) (49975711 / 1000000000000) (49991339 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1650610133 / 500000000) (1650662241 / 500000000) (1857030673 / 1000000000) (1857066961 / 1000000000) (49975711 / 1000000000000) (49991339 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0338 :
    ∀ t ∈ Set.Icc ((1587 / 64000) : ℝ) (397 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1050844104231 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1587 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1587 / 64000)) (1050844104231 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((397 / 16000) : ℝ)) ≤ (131359617953 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (397 / 16000)) (131359617953 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((928533297 / 500000000) : ℝ) ≤ Real.exp (3 * (3301323431 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3301323431 / 1000000000) / 16) (928533297 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((66028553 / 20000000) : ℝ) / 16) ≤ (371420577 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (66028553 / 20000000) / 16) (371420577 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1587 / 64000) : ℝ) (397 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3301323431 / 1000000000) (66028553 / 20000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1587 / 64000) (397 / 16000) (1050844104231 / 1000000000000) (131359617953 / 125000000000) (3301323431 / 1000000000) (66028553 / 20000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1587 / 64000) (397 / 16000) (3301323431 / 1000000000) (66028553 / 20000000) (9992049 / 200000000000) (4997587 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3301323431 / 1000000000) (66028553 / 20000000) (928533297 / 500000000) (371420577 / 200000000) (9992049 / 200000000000) (4997587 / 100000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0339 :
    ∀ t ∈ Set.Icc ((397 / 16000) : ℝ) (1589 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1050876943623 / 1000000000000) : ℝ) ≤ Real.exp (2 * (397 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (397 / 16000)) (1050876943623 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1589 / 64000) : ℝ)) ≤ (1050909784041 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1589 / 64000)) (1050909784041 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((928551259 / 500000000) : ℝ) ≤ Real.exp (3 * (3301426599 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3301426599 / 1000000000) / 16) (928551259 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1650765411 / 500000000) : ℝ) / 16) ≤ (185713881 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1650765411 / 500000000) / 16) (185713881 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((397 / 16000) : ℝ) (1589 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3301426599 / 1000000000) (1650765411 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (397 / 16000) (1589 / 64000) (1050876943623 / 1000000000000) (1050909784041 / 1000000000000) (3301426599 / 1000000000) (1650765411 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (397 / 16000) (1589 / 64000) (3301426599 / 1000000000) (1650765411 / 500000000) (3121549 / 62500000000) (12490101 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3301426599 / 1000000000) (1650765411 / 500000000) (928551259 / 500000000) (185713881 / 100000000) (3121549 / 62500000000) (12490101 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch016 :
    ∀ t ∈ Set.Icc ((1569 / 64000) : ℝ) (1589 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0320
      hpThetaDensityTwoTermCompact_cell0321)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0322
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0323
      hpThetaDensityTwoTermCompact_cell0324)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0325
      hpThetaDensityTwoTermCompact_cell0326)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0327
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0328
      hpThetaDensityTwoTermCompact_cell0329))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0330
      hpThetaDensityTwoTermCompact_cell0331)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0332
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0333
      hpThetaDensityTwoTermCompact_cell0334)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0335
      hpThetaDensityTwoTermCompact_cell0336)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0337
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0338
      hpThetaDensityTwoTermCompact_cell0339)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch016
end HodgeProofHP
