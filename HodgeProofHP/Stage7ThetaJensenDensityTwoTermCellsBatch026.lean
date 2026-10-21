/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0520 :
    ∀ t ∈ Set.Icc ((377 / 12800) : ℝ) (1887 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((530337898861 / 500000000000) : ℝ) ≤ Real.exp (2 * (377 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (377 / 12800)) (530337898861 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1887 / 64000) : ℝ)) ≤ (4143523797 / 3906250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1887 / 64000)) (4143523797 / 3906250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1867852709 / 1000000000) : ℝ) ≤ Real.exp (3 * (16661053 / 5000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (16661053 / 5000000) / 16) (1867852709 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((833104983 / 250000000) : ℝ) / 16) ≤ (233490753 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (833104983 / 250000000) / 16) (233490753 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((377 / 12800) : ℝ) (1887 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (16661053 / 5000000) (833104983 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (377 / 12800) (1887 / 64000) (530337898861 / 500000000000) (4143523797 / 3906250000) (16661053 / 5000000) (833104983 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (377 / 12800) (1887 / 64000) (16661053 / 5000000) (833104983 / 250000000) (9104901 / 200000000000) (2847069 / 62500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (16661053 / 5000000) (833104983 / 250000000) (1867852709 / 1000000000) (233490753 / 125000000) (9104901 / 200000000000) (2847069 / 62500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0521 :
    ∀ t ∈ Set.Icc ((1887 / 64000) : ℝ) (1889 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1060742092031 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1887 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1887 / 64000)) (1060742092031 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1889 / 64000) : ℝ)) ≤ (212161678097 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1889 / 64000)) (212161678097 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1867925651 / 1000000000) : ℝ) ≤ Real.exp (3 * (333241887 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (333241887 / 100000000) / 16) (1867925651 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1666314107 / 500000000) : ℝ) / 16) ≤ (933999487 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1666314107 / 500000000) / 16) (933999487 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1887 / 64000) : ℝ) (1889 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (333241887 / 100000000) (1666314107 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1887 / 64000) (1889 / 64000) (1060742092031 / 1000000000000) (212161678097 / 200000000000) (333241887 / 100000000) (1666314107 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1887 / 64000) (1889 / 64000) (333241887 / 100000000) (1666314107 / 500000000) (11374017 / 250000000000) (45524651 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (333241887 / 100000000) (1666314107 / 500000000) (1867925651 / 1000000000) (933999487 / 500000000) (11374017 / 250000000000) (45524651 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0522 :
    ∀ t ∈ Set.Icc ((1889 / 64000) : ℝ) (1891 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((265202097621 / 250000000000) : ℝ) ≤ Real.exp (2 * (1889 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1889 / 64000)) (265202097621 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1891 / 64000) : ℝ)) ≤ (1060874693081 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1891 / 64000)) (1060874693081 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1867998601 / 1000000000) : ℝ) ≤ Real.exp (3 * (3332627153 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3332627153 / 1000000000) / 16) (1867998601 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((333283651 / 100000000) : ℝ) / 16) ≤ (1868071931 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (333283651 / 100000000) / 16) (1868071931 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1889 / 64000) : ℝ) (1891 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3332627153 / 1000000000) (333283651 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1889 / 64000) (1891 / 64000) (265202097621 / 250000000000) (1060874693081 / 1000000000000) (3332627153 / 1000000000) (333283651 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1889 / 64000) (1891 / 64000) (3332627153 / 1000000000) (333283651 / 100000000) (45467647 / 1000000000000) (22748107 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3332627153 / 1000000000) (333283651 / 100000000) (1867998601 / 1000000000) (1868071931 / 1000000000) (45467647 / 1000000000000) (22748107 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0523 :
    ∀ t ∈ Set.Icc ((1891 / 64000) : ℝ) (1893 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((26521867327 / 25000000000) : ℝ) ≤ Real.exp (2 * (1891 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1891 / 64000)) (26521867327 / 25000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1893 / 64000) : ℝ)) ≤ (530470499911 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1893 / 64000)) (530470499911 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((934035779 / 500000000) : ℝ) ≤ Real.exp (3 * (416604431 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (416604431 / 125000000) / 16) (934035779 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3333044819 / 1000000000) : ℝ) / 16) ≤ (373628979 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3333044819 / 1000000000) / 16) (373628979 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1891 / 64000) : ℝ) (1893 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (416604431 / 125000000) (3333044819 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1891 / 64000) (1893 / 64000) (26521867327 / 25000000000) (530470499911 / 500000000000) (416604431 / 125000000) (3333044819 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1891 / 64000) (1893 / 64000) (416604431 / 125000000) (3333044819 / 1000000000) (22719621 / 500000000000) (45467793 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (416604431 / 125000000) (3333044819 / 1000000000) (934035779 / 500000000) (373628979 / 200000000) (22719621 / 500000000000) (45467793 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0524 :
    ∀ t ∈ Set.Icc ((1893 / 64000) : ℝ) (379 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1060940999821 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1893 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1893 / 64000)) (1060940999821 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((379 / 12800) : ℝ)) ≤ (530503655353 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (379 / 12800)) (530503655353 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((934072261 / 500000000) : ℝ) ≤ Real.exp (3 * (3333043757 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3333043757 / 1000000000) / 16) (934072261 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3333253141 / 1000000000) : ℝ) / 16) ≤ (1868217867 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3333253141 / 1000000000) / 16) (1868217867 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1893 / 64000) : ℝ) (379 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3333043757 / 1000000000) (3333253141 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1893 / 64000) (379 / 12800) (1060940999821 / 1000000000000) (530503655353 / 500000000000) (3333043757 / 1000000000) (3333253141 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1893 / 64000) (379 / 12800) (3333043757 / 1000000000) (3333253141 / 1000000000) (45410853 / 1000000000000) (11359847 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3333043757 / 1000000000) (3333253141 / 1000000000) (934072261 / 500000000) (1868217867 / 1000000000) (45410853 / 1000000000000) (11359847 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0525 :
    ∀ t ∈ Set.Icc ((379 / 12800) : ℝ) (1897 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((212201462141 / 200000000000) : ℝ) ≤ Real.exp (2 * (379 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (379 / 12800)) (212201462141 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1897 / 64000) : ℝ)) ≤ (132634203217 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1897 / 64000)) (132634203217 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((934108747 / 500000000) : ℝ) ≤ Real.exp (3 * (3333252079 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3333252079 / 1000000000) / 16) (934108747 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((833365369 / 250000000) : ℝ) / 16) ≤ (934145423 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (833365369 / 250000000) / 16) (934145423 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((379 / 12800) : ℝ) (1897 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3333252079 / 1000000000) (833365369 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (379 / 12800) (1897 / 64000) (212201462141 / 200000000000) (132634203217 / 125000000000) (3333252079 / 1000000000) (833365369 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (379 / 12800) (1897 / 64000) (3333252079 / 1000000000) (833365369 / 250000000) (567281 / 12500000000) (45410999 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3333252079 / 1000000000) (833365369 / 250000000) (934108747 / 500000000) (934145423 / 500000000) (567281 / 12500000000) (45410999 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0526 :
    ∀ t ∈ Set.Icc ((1897 / 64000) : ℝ) (1899 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((212214725147 / 200000000000) : ℝ) ≤ Real.exp (2 * (1897 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1897 / 64000)) (212214725147 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1899 / 64000) : ℝ)) ≤ (106113994491 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1899 / 64000)) (106113994491 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1868290473 / 1000000000) : ℝ) ≤ Real.exp (3 * (1666730207 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1666730207 / 500000000) / 16) (1868290473 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3333669823 / 1000000000) : ℝ) / 16) ≤ (1868363833 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3333669823 / 1000000000) / 16) (1868363833 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1897 / 64000) : ℝ) (1899 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1666730207 / 500000000) (3333669823 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1897 / 64000) (1899 / 64000) (212214725147 / 200000000000) (106113994491 / 100000000000) (1666730207 / 500000000) (3333669823 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1897 / 64000) (1899 / 64000) (1666730207 / 500000000) (3333669823 / 1000000000) (22677061 / 500000000000) (22691313 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1666730207 / 500000000) (3333669823 / 1000000000) (1868290473 / 1000000000) (1868363833 / 1000000000) (22677061 / 500000000000) (22691313 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0527 :
    ∀ t ∈ Set.Icc ((1899 / 64000) : ℝ) (1901 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1061139944909 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1899 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1899 / 64000)) (1061139944909 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1901 / 64000) : ℝ)) ≤ (1061206268229 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1901 / 64000)) (1061206268229 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((93418173 / 50000000) : ℝ) ≤ Real.exp (3 * (3333668761 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3333668761 / 1000000000) / 16) (93418173 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((416734773 / 125000000) : ℝ) / 16) ≤ (1868436827 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (416734773 / 125000000) / 16) (1868436827 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1899 / 64000) : ℝ) (1901 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3333668761 / 1000000000) (416734773 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1899 / 64000) (1901 / 64000) (1061139944909 / 1000000000000) (1061206268229 / 1000000000000) (3333668761 / 1000000000) (416734773 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1899 / 64000) (1901 / 64000) (3333668761 / 1000000000) (416734773 / 125000000) (45325781 / 1000000000000) (11338567 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3333668761 / 1000000000) (416734773 / 125000000) (93418173 / 50000000) (1868436827 / 1000000000) (45325781 / 1000000000000) (11338567 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0528 :
    ∀ t ∈ Set.Icc ((1901 / 64000) : ℝ) (1903 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((265301567057 / 250000000000) : ℝ) ≤ Real.exp (2 * (1901 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1901 / 64000)) (265301567057 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1903 / 64000) : ℝ)) ≤ (1061272595693 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1903 / 64000)) (1061272595693 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((934218227 / 500000000) : ℝ) ≤ Real.exp (3 * (1666938561 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1666938561 / 500000000) / 16) (934218227 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1667043279 / 500000000) : ℝ) / 16) ≤ (467127457 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1667043279 / 500000000) / 16) (467127457 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1901 / 64000) : ℝ) (1903 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1666938561 / 500000000) (1667043279 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1901 / 64000) (1903 / 64000) (265301567057 / 250000000000) (1061272595693 / 1000000000000) (1666938561 / 500000000) (1667043279 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1901 / 64000) (1903 / 64000) (1666938561 / 500000000) (1667043279 / 500000000) (2831091 / 62500000000) (45325927 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1666938561 / 500000000) (1667043279 / 500000000) (934218227 / 500000000) (467127457 / 250000000) (2831091 / 62500000000) (45325927 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0529 :
    ∀ t ∈ Set.Icc ((1903 / 64000) : ℝ) (381 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((265318148923 / 250000000000) : ℝ) ≤ Real.exp (2 * (1903 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1903 / 64000)) (265318148923 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((381 / 12800) : ℝ)) ≤ (1061338927303 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (381 / 12800)) (1061338927303 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((373701891 / 200000000) : ℝ) ≤ Real.exp (3 * (416760687 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (416760687 / 125000000) / 16) (373701891 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((666858989 / 200000000) : ℝ) / 16) ≤ (1868582837 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (666858989 / 200000000) / 16) (1868582837 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1903 / 64000) : ℝ) (381 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (416760687 / 125000000) (666858989 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1903 / 64000) (381 / 12800) (265318148923 / 250000000000) (1061338927303 / 1000000000000) (416760687 / 125000000) (666858989 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1903 / 64000) (381 / 12800) (416760687 / 125000000) (666858989 / 200000000) (45269147 / 1000000000000) (22648801 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (416760687 / 125000000) (666858989 / 200000000) (373701891 / 200000000) (1868582837 / 1000000000) (45269147 / 1000000000000) (22648801 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0530 :
    ∀ t ∈ Set.Icc ((381 / 12800) : ℝ) (1907 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((530669463651 / 500000000000) : ℝ) ≤ Real.exp (2 * (381 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (381 / 12800)) (530669463651 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1907 / 64000) : ℝ)) ≤ (1061405263059 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1907 / 64000)) (1061405263059 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((29196601 / 15625000) : ℝ) ≤ Real.exp (3 * (3334293883 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3334293883 / 1000000000) / 16) (29196601 / 15625000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((666900669 / 200000000) : ℝ) / 16) ≤ (1868655853 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (666900669 / 200000000) / 16) (1868655853 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((381 / 12800) : ℝ) (1907 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3334293883 / 1000000000) (666900669 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (381 / 12800) (1907 / 64000) (530669463651 / 500000000000) (1061405263059 / 1000000000000) (3334293883 / 1000000000) (666900669 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (381 / 12800) (1907 / 64000) (3334293883 / 1000000000) (666900669 / 200000000) (45240853 / 1000000000000) (11317323 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3334293883 / 1000000000) (666900669 / 200000000) (29196601 / 15625000) (1868655853 / 1000000000) (45240853 / 1000000000000) (11317323 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0531 :
    ∀ t ∈ Set.Icc ((1907 / 64000) : ℝ) (1909 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((530702631529 / 500000000000) : ℝ) ≤ Real.exp (2 * (1907 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1907 / 64000)) (530702631529 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1909 / 64000) : ℝ)) ≤ (1061471602961 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1909 / 64000)) (1061471602961 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((46716387 / 25000000) : ℝ) ≤ Real.exp (3 * (3334502283 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3334502283 / 1000000000) / 16) (46716387 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1667355879 / 500000000) : ℝ) / 16) ≤ (1868728877 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1667355879 / 500000000) / 16) (1868728877 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1907 / 64000) : ℝ) (1909 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3334502283 / 1000000000) (1667355879 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1907 / 64000) (1909 / 64000) (530702631529 / 500000000000) (1061471602961 / 1000000000000) (3334502283 / 1000000000) (1667355879 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1907 / 64000) (1909 / 64000) (3334502283 / 1000000000) (1667355879 / 500000000) (1412893 / 31250000000) (45240999 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3334502283 / 1000000000) (1667355879 / 500000000) (46716387 / 25000000) (1868728877 / 1000000000) (1412893 / 31250000000) (45240999 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0532 :
    ∀ t ∈ Set.Icc ((1909 / 64000) : ℝ) (1911 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((13268395037 / 12500000000) : ℝ) ≤ Real.exp (2 * (1909 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1909 / 64000)) (13268395037 / 12500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1911 / 64000) : ℝ)) ≤ (106153794701 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1911 / 64000)) (106153794701 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((233591063 / 125000000) : ℝ) ≤ Real.exp (3 * (416838837 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (416838837 / 125000000) / 16) (233591063 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((416865023 / 125000000) : ℝ) / 16) ≤ (467200477 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (416865023 / 125000000) / 16) (467200477 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1909 / 64000) : ℝ) (1911 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (416838837 / 125000000) (416865023 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1909 / 64000) (1911 / 64000) (13268395037 / 12500000000) (106153794701 / 100000000000) (416838837 / 125000000) (416865023 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1909 / 64000) (1911 / 64000) (416838837 / 125000000) (416865023 / 125000000) (22592157 / 500000000000) (45212721 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (416838837 / 125000000) (416865023 / 125000000) (233591063 / 125000000) (467200477 / 250000000) (22592157 / 500000000000) (45212721 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0533 :
    ∀ t ∈ Set.Icc ((1911 / 64000) : ℝ) (1913 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1061537947009 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1911 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1911 / 64000)) (1061537947009 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1913 / 64000) : ℝ)) ≤ (212320859041 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1913 / 64000)) (212320859041 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((373760307 / 200000000) : ℝ) ≤ Real.exp (3 * (1667459561 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1667459561 / 500000000) / 16) (373760307 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3335128623 / 1000000000) : ℝ) / 16) ≤ (1868874947 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3335128623 / 1000000000) / 16) (1868874947 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1911 / 64000) : ℝ) (1913 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1667459561 / 500000000) (3335128623 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1911 / 64000) (1913 / 64000) (1061537947009 / 1000000000000) (212320859041 / 200000000000) (1667459561 / 500000000) (3335128623 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1911 / 64000) (1913 / 64000) (1667459561 / 500000000) (3335128623 / 1000000000) (11289017 / 250000000000) (45184459 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1667459561 / 500000000) (3335128623 / 1000000000) (373760307 / 200000000) (1868874947 / 1000000000) (11289017 / 250000000000) (45184459 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0534 :
    ∀ t ∈ Set.Icc ((1913 / 64000) : ℝ) (383 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((265401073801 / 250000000000) : ℝ) ≤ Real.exp (2 * (1913 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1913 / 64000)) (265401073801 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((383 / 12800) : ℝ)) ≤ (1061670647547 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (383 / 12800)) (1061670647547 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1868874573 / 1000000000) : ℝ) ≤ Real.exp (3 * (83378189 / 25000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (83378189 / 25000000) / 16) (1868874573 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((133413483 / 40000000) : ℝ) / 16) ≤ (1868947993 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (133413483 / 40000000) / 16) (1868947993 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1913 / 64000) : ℝ) (383 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (83378189 / 25000000) (133413483 / 40000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1913 / 64000) (383 / 12800) (265401073801 / 250000000000) (1061670647547 / 1000000000000) (83378189 / 25000000) (133413483 / 40000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1913 / 64000) (383 / 12800) (83378189 / 25000000) (133413483 / 40000000) (22563919 / 500000000000) (22578107 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (83378189 / 25000000) (133413483 / 40000000) (1868874573 / 1000000000) (1868947993 / 1000000000) (22563919 / 500000000000) (22578107 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0535 :
    ∀ t ∈ Set.Icc ((383 / 12800) : ℝ) (1917 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((530835323773 / 500000000000) : ℝ) ≤ Real.exp (2 * (383 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (383 / 12800)) (530835323773 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1917 / 64000) : ℝ)) ≤ (265434251009 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1917 / 64000)) (265434251009 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1868947619 / 1000000000) : ℝ) ≤ Real.exp (3 * (833834003 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (833834003 / 250000000) / 16) (1868947619 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((166777277 / 50000000) : ℝ) / 16) ≤ (934510523 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (166777277 / 50000000) / 16) (934510523 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((383 / 12800) : ℝ) (1917 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (833834003 / 250000000) (166777277 / 50000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (383 / 12800) (1917 / 64000) (530835323773 / 500000000000) (265434251009 / 250000000000) (833834003 / 250000000) (166777277 / 50000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (383 / 12800) (1917 / 64000) (833834003 / 250000000) (166777277 / 50000000) (360797 / 8000000000) (2820499 / 62500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (833834003 / 250000000) (166777277 / 50000000) (1868947619 / 1000000000) (934510523 / 500000000) (360797 / 8000000000) (2820499 / 62500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0536 :
    ∀ t ∈ Set.Icc ((1917 / 64000) : ℝ) (1919 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((212347400807 / 200000000000) : ℝ) ≤ Real.exp (2 * (1917 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1917 / 64000)) (212347400807 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1919 / 64000) : ℝ)) ≤ (16590677573 / 15625000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1919 / 64000)) (16590677573 / 15625000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1869020673 / 1000000000) : ℝ) ≤ Real.exp (3 * (3335544477 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3335544477 / 1000000000) / 16) (1869020673 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1667877009 / 500000000) : ℝ) / 16) ≤ (1869094107 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1667877009 / 500000000) / 16) (1869094107 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1917 / 64000) : ℝ) (1919 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3335544477 / 1000000000) (1667877009 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1917 / 64000) (1919 / 64000) (212347400807 / 200000000000) (16590677573 / 15625000000) (3335544477 / 1000000000) (1667877009 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1917 / 64000) (1919 / 64000) (3335544477 / 1000000000) (1667877009 / 500000000) (45071427 / 1000000000000) (4509977 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3335544477 / 1000000000) (1667877009 / 500000000) (1869020673 / 1000000000) (1869094107 / 1000000000) (45071427 / 1000000000000) (4509977 / 100000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0537 :
    ∀ t ∈ Set.Icc ((1919 / 64000) : ℝ) (1921 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1061803364671 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1919 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1919 / 64000)) (1061803364671 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1921 / 64000) : ℝ)) ≤ (66366858091 / 62500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1921 / 64000)) (66366858091 / 62500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((934546867 / 500000000) : ℝ) ≤ Real.exp (3 * (833938239 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (833938239 / 250000000) / 16) (934546867 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3335962509 / 1000000000) : ℝ) / 16) ≤ (74766687 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3335962509 / 1000000000) / 16) (74766687 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1919 / 64000) : ℝ) (1921 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (833938239 / 250000000) (3335962509 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1919 / 64000) (1921 / 64000) (1061803364671 / 1000000000000) (66366858091 / 62500000000) (833938239 / 250000000) (3335962509 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1919 / 64000) (1921 / 64000) (833938239 / 250000000) (3335962509 / 1000000000) (11260811 / 250000000000) (45071571 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (833938239 / 250000000) (3335962509 / 1000000000) (934546867 / 500000000) (74766687 / 40000000) (11260811 / 250000000000) (45071571 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0538 :
    ∀ t ∈ Set.Icc ((1921 / 64000) : ℝ) (1923 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((212373945891 / 200000000000) : ℝ) ≤ Real.exp (2 * (1921 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1921 / 64000)) (212373945891 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1923 / 64000) : ℝ)) ≤ (1061936098389 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1923 / 64000)) (1061936098389 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((934583401 / 500000000) : ℝ) ≤ Real.exp (3 * (3335961447 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3335961447 / 1000000000) / 16) (934583401 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1668085507 / 500000000) : ℝ) / 16) ≤ (1869240251 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1668085507 / 500000000) / 16) (1869240251 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1921 / 64000) : ℝ) (1923 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3335961447 / 1000000000) (1668085507 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1921 / 64000) (1923 / 64000) (212373945891 / 200000000000) (1061936098389 / 1000000000000) (3335961447 / 1000000000) (1668085507 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1921 / 64000) (1923 / 64000) (3335961447 / 1000000000) (1668085507 / 500000000) (22507539 / 500000000000) (45043389 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3335961447 / 1000000000) (1668085507 / 500000000) (934583401 / 500000000) (1869240251 / 1000000000) (22507539 / 500000000000) (45043389 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0539 :
    ∀ t ∈ Set.Icc ((1923 / 64000) : ℝ) (77 / 2560), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((265484024597 / 250000000000) : ℝ) ≤ Real.exp (2 * (1923 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1923 / 64000)) (265484024597 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((77 / 2560) : ℝ)) ≤ (1062002471469 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (77 / 2560)) (1062002471469 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1869239877 / 1000000000) : ℝ) ≤ Real.exp (3 * (3336169951 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3336169951 / 1000000000) / 16) (1869239877 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3336379531 / 1000000000) : ℝ) / 16) ≤ (934656667 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3336379531 / 1000000000) / 16) (934656667 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1923 / 64000) : ℝ) (77 / 2560),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3336169951 / 1000000000) (3336379531 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1923 / 64000) (77 / 2560) (265484024597 / 250000000000) (1062002471469 / 1000000000000) (3336169951 / 1000000000) (3336379531 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1923 / 64000) (77 / 2560) (3336169951 / 1000000000) (3336379531 / 1000000000) (2811683 / 62500000000) (45015223 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3336169951 / 1000000000) (3336379531 / 1000000000) (1869239877 / 1000000000) (934656667 / 500000000) (2811683 / 62500000000) (45015223 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch026 :
    ∀ t ∈ Set.Icc ((377 / 12800) : ℝ) (77 / 2560),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0520
      hpThetaDensityTwoTermCompact_cell0521)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0522
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0523
      hpThetaDensityTwoTermCompact_cell0524)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0525
      hpThetaDensityTwoTermCompact_cell0526)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0527
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0528
      hpThetaDensityTwoTermCompact_cell0529))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0530
      hpThetaDensityTwoTermCompact_cell0531)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0532
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0533
      hpThetaDensityTwoTermCompact_cell0534)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0535
      hpThetaDensityTwoTermCompact_cell0536)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0537
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0538
      hpThetaDensityTwoTermCompact_cell0539)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch026
end HodgeProofHP
