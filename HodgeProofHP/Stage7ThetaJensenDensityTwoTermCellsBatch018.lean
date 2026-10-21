/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0360 :
    ∀ t ∈ Set.Icc ((1609 / 64000) : ℝ) (161 / 6400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((525783403977 / 500000000000) : ℝ) ≤ Real.exp (2 * (1609 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1609 / 64000)) (525783403977 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((161 / 6400) : ℝ)) ≤ (1051599669931 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (161 / 6400)) (1051599669931 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((185785733 / 100000000) : ℝ) ≤ Real.exp (3 * (3303593871 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3303593871 / 1000000000) / 16) (185785733 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1651849081 / 500000000) : ℝ) / 16) ≤ (1857893661 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1651849081 / 500000000) / 16) (1857893661 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1609 / 64000) : ℝ) (161 / 6400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3303593871 / 1000000000) (1651849081 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1609 / 64000) (161 / 6400) (525783403977 / 500000000000) (1051599669931 / 1000000000000) (3303593871 / 1000000000) (1651849081 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1609 / 64000) (161 / 6400) (3303593871 / 1000000000) (1651849081 / 500000000) (6202637 / 125000000000) (397093 / 8000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3303593871 / 1000000000) (1651849081 / 500000000) (185785733 / 100000000) (1857893661 / 1000000000) (6202637 / 125000000000) (397093 / 8000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0361 :
    ∀ t ∈ Set.Icc ((161 / 6400) : ℝ) (1611 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((105159966993 / 100000000000) : ℝ) ≤ Real.exp (2 * (161 / 6400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (161 / 6400)) (105159966993 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1611 / 64000) : ℝ)) ≤ (525816266467 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1611 / 64000)) (525816266467 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1857893293 / 1000000000) : ℝ) ≤ Real.exp (3 * (330369711 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (330369711 / 100000000) / 16) (1857893293 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((660760281 / 200000000) : ℝ) / 16) ≤ (928964813 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (660760281 / 200000000) / 16) (928964813 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((161 / 6400) : ℝ) (1611 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (330369711 / 100000000) (660760281 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (161 / 6400) (1611 / 64000) (105159966993 / 100000000000) (525816266467 / 500000000000) (330369711 / 100000000) (660760281 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (161 / 6400) (1611 / 64000) (330369711 / 100000000) (660760281 / 200000000) (49605729 / 1000000000000) (24810627 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (330369711 / 100000000) (660760281 / 200000000) (1857893293 / 1000000000) (928964813 / 500000000) (49605729 / 1000000000000) (24810627 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0362 :
    ∀ t ∈ Set.Icc ((1611 / 64000) : ℝ) (403 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1051632532933 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1611 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1611 / 64000)) (1051632532933 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((403 / 16000) : ℝ)) ≤ (262916349241 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (403 / 16000)) (262916349241 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1857929259 / 1000000000) : ℝ) ≤ Real.exp (3 * (103243761 / 31250000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (103243761 / 31250000) / 16) (1857929259 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((66078093 / 20000000) : ℝ) / 16) ≤ (1857965593 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (66078093 / 20000000) / 16) (1857965593 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1611 / 64000) : ℝ) (403 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (103243761 / 31250000) (66078093 / 20000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1611 / 64000) (403 / 16000) (1051632532933 / 1000000000000) (262916349241 / 250000000000) (103243761 / 31250000) (66078093 / 20000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1611 / 64000) (403 / 16000) (103243761 / 31250000) (66078093 / 20000000) (49590367 / 1000000000000) (49605887 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (103243761 / 31250000) (66078093 / 20000000) (1857929259 / 1000000000) (1857965593 / 1000000000) (49590367 / 1000000000000) (49605887 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0363 :
    ∀ t ∈ Set.Icc ((403 / 16000) : ℝ) (1613 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1051665396963 / 1000000000000) : ℝ) ≤ Real.exp (2 * (403 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (403 / 16000)) (1051665396963 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1613 / 64000) : ℝ)) ≤ (525849131011 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1613 / 64000)) (525849131011 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((928982613 / 500000000) : ℝ) ≤ Real.exp (3 * (3303903597 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3303903597 / 1000000000) / 16) (928982613 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3304007899 / 1000000000) : ℝ) / 16) ≤ (929000781 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3304007899 / 1000000000) / 16) (929000781 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((403 / 16000) : ℝ) (1613 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3303903597 / 1000000000) (3304007899 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (403 / 16000) (1613 / 64000) (1051665396963 / 1000000000000) (525849131011 / 500000000000) (3303903597 / 1000000000) (3304007899 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (403 / 16000) (1613 / 64000) (3303903597 / 1000000000) (3304007899 / 1000000000) (49575009 / 1000000000000) (1983621 / 40000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3303903597 / 1000000000) (3304007899 / 1000000000) (928982613 / 500000000) (929000781 / 500000000) (49575009 / 1000000000000) (1983621 / 40000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0364 :
    ∀ t ∈ Set.Icc ((1613 / 64000) : ℝ) (807 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1051698262021 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1613 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1613 / 64000)) (1051698262021 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((807 / 32000) : ℝ)) ≤ (525865564053 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (807 / 32000)) (525865564053 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((371600239 / 200000000) : ℝ) ≤ Real.exp (3 * (1652003423 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1652003423 / 500000000) / 16) (371600239 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((66082223 / 20000000) : ℝ) / 16) ≤ (1858037533 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (66082223 / 20000000) / 16) (1858037533 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1613 / 64000) : ℝ) (807 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1652003423 / 500000000) (66082223 / 20000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1613 / 64000) (807 / 32000) (1051698262021 / 1000000000000) (525865564053 / 500000000000) (1652003423 / 500000000) (66082223 / 20000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1613 / 64000) (807 / 32000) (1652003423 / 500000000) (66082223 / 20000000) (9911931 / 200000000000) (24787583 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1652003423 / 500000000) (66082223 / 20000000) (371600239 / 200000000) (1858037533 / 1000000000) (9911931 / 200000000000) (24787583 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0365 :
    ∀ t ∈ Set.Icc ((807 / 32000) : ℝ) (323 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((210346225621 / 200000000000) : ℝ) ≤ Real.exp (2 * (807 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (807 / 32000)) (210346225621 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((323 / 12800) : ℝ)) ≤ (1051763995217 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (323 / 12800)) (1051763995217 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((371607433 / 200000000) : ℝ) ≤ Real.exp (3 * (1652055049 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1652055049 / 500000000) / 16) (371607433 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1652107203 / 500000000) : ℝ) / 16) ≤ (929036753 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1652107203 / 500000000) / 16) (929036753 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((807 / 32000) : ℝ) (323 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1652055049 / 500000000) (1652107203 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (807 / 32000) (323 / 12800) (210346225621 / 200000000000) (1051763995217 / 1000000000000) (1652055049 / 500000000) (1652107203 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (807 / 32000) (323 / 12800) (1652055049 / 500000000) (1652107203 / 500000000) (9908861 / 200000000000) (49559813 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1652055049 / 500000000) (1652107203 / 500000000) (371607433 / 200000000) (929036753 / 500000000) (9908861 / 200000000000) (49559813 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0366 :
    ∀ t ∈ Set.Icc ((323 / 12800) : ℝ) (101 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((65735249701 / 62500000000) : ℝ) ≤ Real.exp (2 * (323 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (323 / 12800)) (65735249701 / 62500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((101 / 4000) : ℝ)) ≤ (262949215839 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (101 / 4000)) (262949215839 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((929036569 / 500000000) : ℝ) ≤ Real.exp (3 * (3304213353 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3304213353 / 1000000000) / 16) (929036569 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((103259927 / 31250000) : ℝ) / 16) ≤ (46452737 / 25000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (103259927 / 31250000) / 16) (46452737 / 25000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((323 / 12800) : ℝ) (101 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3304213353 / 1000000000) (103259927 / 31250000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (323 / 12800) (101 / 4000) (65735249701 / 62500000000) (262949215839 / 250000000000) (3304213353 / 1000000000) (103259927 / 31250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (323 / 12800) (101 / 4000) (3304213353 / 1000000000) (103259927 / 31250000) (77389 / 1562500000) (49544463 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3304213353 / 1000000000) (103259927 / 31250000) (929036569 / 500000000) (46452737 / 25000000) (77389 / 1562500000) (49544463 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0367 :
    ∀ t ∈ Set.Icc ((101 / 4000) : ℝ) (1617 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((210359372671 / 200000000000) : ℝ) ≤ Real.exp (2 * (101 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (101 / 4000)) (210359372671 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1617 / 64000) : ℝ)) ≤ (1051829732521 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1617 / 64000)) (1051829732521 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((232263639 / 125000000) : ℝ) ≤ Real.exp (3 * (3304316611 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3304316611 / 1000000000) / 16) (232263639 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((132176837 / 40000000) : ℝ) / 16) ≤ (116134091 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (132176837 / 40000000) / 16) (116134091 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((101 / 4000) : ℝ) (1617 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3304316611 / 1000000000) (132176837 / 40000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (101 / 4000) (1617 / 64000) (210359372671 / 200000000000) (1051829732521 / 1000000000000) (3304316611 / 1000000000) (132176837 / 40000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (101 / 4000) (1617 / 64000) (3304316611 / 1000000000) (132176837 / 40000000) (49513619 / 1000000000000) (24764559 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3304316611 / 1000000000) (132176837 / 40000000) (232263639 / 125000000) (116134091 / 62500000) (49513619 / 1000000000000) (24764559 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0368 :
    ∀ t ∈ Set.Icc ((1617 / 64000) : ℝ) (809 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((26295743313 / 25000000000) : ℝ) ≤ Real.exp (2 * (1617 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1617 / 64000)) (26295743313 / 25000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((809 / 32000) : ℝ)) ≤ (525931301357 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (809 / 32000)) (525931301357 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1858145089 / 1000000000) : ℝ) ≤ Real.exp (3 * (3304419873 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3304419873 / 1000000000) / 16) (1858145089 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((330452419 / 100000000) : ℝ) / 16) ≤ (929090717 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (330452419 / 100000000) / 16) (929090717 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1617 / 64000) : ℝ) (809 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3304419873 / 1000000000) (330452419 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1617 / 64000) (809 / 32000) (26295743313 / 25000000000) (525931301357 / 500000000000) (3304419873 / 1000000000) (330452419 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1617 / 64000) (809 / 32000) (3304419873 / 1000000000) (330452419 / 100000000) (49498283 / 1000000000000) (49513777 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3304419873 / 1000000000) (330452419 / 100000000) (1858145089 / 1000000000) (929090717 / 500000000) (49498283 / 1000000000000) (49513777 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0369 :
    ∀ t ∈ Set.Icc ((809 / 32000) : ℝ) (1619 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1051862602713 / 1000000000000) : ℝ) ≤ Real.exp (2 * (809 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (809 / 32000)) (1051862602713 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1619 / 64000) : ℝ)) ≤ (525947736967 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1619 / 64000)) (525947736967 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((929090533 / 500000000) : ℝ) ≤ Real.exp (3 * (3304523137 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3304523137 / 1000000000) / 16) (929090533 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1652313729 / 500000000) : ℝ) / 16) ≤ (929108707 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1652313729 / 500000000) / 16) (929108707 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((809 / 32000) : ℝ) (1619 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3304523137 / 1000000000) (1652313729 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (809 / 32000) (1619 / 64000) (1051862602713 / 1000000000000) (525947736967 / 500000000000) (3304523137 / 1000000000) (1652313729 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (809 / 32000) (1619 / 64000) (3304523137 / 1000000000) (1652313729 / 500000000) (989659 / 20000000000) (49498441 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3304523137 / 1000000000) (1652313729 / 500000000) (929090533 / 500000000) (929108707 / 500000000) (989659 / 20000000000) (49498441 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0370 :
    ∀ t ∈ Set.Icc ((1619 / 64000) : ℝ) (81 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1051895473933 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1619 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1619 / 64000)) (1051895473933 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((81 / 3200) : ℝ)) ≤ (1051928346181 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (81 / 3200)) (1051928346181 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((929108523 / 500000000) : ℝ) ≤ Real.exp (3 * (660925281 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (660925281 / 200000000) / 16) (929108523 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3304730729 / 1000000000) : ℝ) / 16) ≤ (464563349 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3304730729 / 1000000000) / 16) (464563349 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1619 / 64000) : ℝ) (81 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (660925281 / 200000000) (3304730729 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1619 / 64000) (81 / 3200) (1051895473933 / 1000000000000) (1051928346181 / 1000000000000) (660925281 / 200000000) (3304730729 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1619 / 64000) (81 / 3200) (660925281 / 200000000) (3304730729 / 1000000000) (24733811 / 500000000000) (12370777 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (660925281 / 200000000) (3304730729 / 1000000000) (929108523 / 500000000) (464563349 / 250000000) (24733811 / 500000000000) (12370777 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0371 :
    ∀ t ∈ Set.Icc ((81 / 3200) : ℝ) (1621 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((52596417309 / 50000000000) : ℝ) ≤ Real.exp (2 * (81 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (81 / 3200)) (52596417309 / 50000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1621 / 64000) : ℝ)) ≤ (210392243891 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1621 / 64000)) (210392243891 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((464563257 / 250000000) : ℝ) ≤ Real.exp (3 * (826182419 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (826182419 / 250000000) / 16) (464563257 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((826208501 / 250000000) : ℝ) / 16) ≤ (1858289379 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (826208501 / 250000000) / 16) (1858289379 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((81 / 3200) : ℝ) (1621 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (826182419 / 250000000) (826208501 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (81 / 3200) (1621 / 64000) (52596417309 / 50000000000) (210392243891 / 200000000000) (826182419 / 250000000) (826208501 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (81 / 3200) (1621 / 64000) (826182419 / 250000000) (826208501 / 250000000) (24726149 / 500000000000) (2473389 / 50000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (826182419 / 250000000) (826208501 / 250000000) (464563257 / 250000000) (1858289379 / 1000000000) (24726149 / 500000000000) (2473389 / 50000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0372 :
    ∀ t ∈ Set.Icc ((1621 / 64000) : ℝ) (811 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((525980609727 / 500000000000) : ℝ) ≤ Real.exp (2 * (1621 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1621 / 64000)) (525980609727 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((811 / 32000) : ℝ)) ≤ (1051994093757 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (811 / 32000)) (1051994093757 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1858289011 / 1000000000) : ℝ) ≤ Real.exp (3 * (3304832951 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3304832951 / 1000000000) / 16) (1858289011 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3304937281 / 1000000000) : ℝ) / 16) ≤ (464581341 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3304937281 / 1000000000) / 16) (464581341 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1621 / 64000) : ℝ) (811 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3304832951 / 1000000000) (3304937281 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1621 / 64000) (811 / 32000) (525980609727 / 500000000000) (1051994093757 / 1000000000000) (3304832951 / 1000000000) (3304937281 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1621 / 64000) (811 / 32000) (3304832951 / 1000000000) (3304937281 / 1000000000) (49436979 / 1000000000000) (6181557 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3304832951 / 1000000000) (3304937281 / 1000000000) (1858289011 / 1000000000) (464581341 / 250000000) (49436979 / 1000000000000) (6181557 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0373 :
    ∀ t ∈ Set.Icc ((811 / 32000) : ℝ) (1623 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((262998523439 / 250000000000) : ℝ) ≤ Real.exp (2 * (811 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (811 / 32000)) (262998523439 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1623 / 64000) : ℝ)) ≤ (526013484543 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1623 / 64000)) (526013484543 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((464581249 / 250000000) : ℝ) ≤ Real.exp (3 * (826234057 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (826234057 / 250000000) / 16) (464581249 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1652520281 / 500000000) : ℝ) / 16) ≤ (232295169 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1652520281 / 500000000) / 16) (232295169 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((811 / 32000) : ℝ) (1623 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (826234057 / 250000000) (1652520281 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (811 / 32000) (1623 / 64000) (262998523439 / 250000000000) (526013484543 / 500000000000) (826234057 / 250000000) (1652520281 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (811 / 32000) (1623 / 64000) (826234057 / 250000000) (1652520281 / 500000000) (49421663 / 1000000000000) (3089821 / 62500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (826234057 / 250000000) (1652520281 / 500000000) (464581249 / 250000000) (232295169 / 125000000) (49421663 / 1000000000000) (3089821 / 62500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0374 :
    ∀ t ∈ Set.Icc ((1623 / 64000) : ℝ) (203 / 8000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((210405393817 / 200000000000) : ℝ) ≤ Real.exp (2 * (1623 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1623 / 64000)) (210405393817 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((203 / 8000) : ℝ)) ≤ (1052059845443 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (203 / 8000)) (1052059845443 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((232295123 / 125000000) : ℝ) ≤ Real.exp (3 * (3305039509 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3305039509 / 1000000000) / 16) (232295123 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3305143847 / 1000000000) : ℝ) / 16) ≤ (1858397341 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3305143847 / 1000000000) / 16) (1858397341 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1623 / 64000) : ℝ) (203 / 8000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3305039509 / 1000000000) (3305143847 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1623 / 64000) (203 / 8000) (210405393817 / 200000000000) (1052059845443 / 1000000000000) (3305039509 / 1000000000) (3305143847 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1623 / 64000) (203 / 8000) (3305039509 / 1000000000) (3305143847 / 1000000000) (3087897 / 62500000000) (49421821 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3305039509 / 1000000000) (3305143847 / 1000000000) (232295123 / 125000000) (1858397341 / 1000000000) (3087897 / 62500000000) (49421821 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0375 :
    ∀ t ∈ Set.Icc ((203 / 8000) : ℝ) (13 / 512), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((526029922721 / 500000000000) : ℝ) ≤ Real.exp (2 * (203 / 8000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (203 / 8000)) (526029922721 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((13 / 512) : ℝ)) ≤ (1052092722827 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (13 / 512)) (1052092722827 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1858396973 / 1000000000) : ℝ) ≤ Real.exp (3 * (3305142793 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3305142793 / 1000000000) / 16) (1858396973 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1652623567 / 500000000) : ℝ) / 16) ≤ (1858433331 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1652623567 / 500000000) / 16) (1858433331 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((203 / 8000) : ℝ) (13 / 512),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3305142793 / 1000000000) (1652623567 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (203 / 8000) (13 / 512) (526029922721 / 500000000000) (1052092722827 / 1000000000000) (3305142793 / 1000000000) (1652623567 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (203 / 8000) (13 / 512) (3305142793 / 1000000000) (1652623567 / 500000000) (24695523 / 500000000000) (4940651 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3305142793 / 1000000000) (1652623567 / 500000000) (1858396973 / 1000000000) (1858433331 / 1000000000) (24695523 / 500000000000) (4940651 / 100000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0376 :
    ∀ t ∈ Set.Icc ((13 / 512) : ℝ) (813 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((526046361413 / 500000000000) : ℝ) ≤ Real.exp (2 * (13 / 512)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (13 / 512)) (526046361413 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((813 / 32000) : ℝ)) ≤ (526062800619 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (813 / 32000)) (526062800619 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((464608241 / 250000000) : ℝ) ≤ Real.exp (3 * (3305246081 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3305246081 / 1000000000) / 16) (464608241 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((413168803 / 125000000) : ℝ) / 16) ≤ (464617331 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (413168803 / 125000000) / 16) (464617331 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((13 / 512) : ℝ) (813 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3305246081 / 1000000000) (413168803 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (13 / 512) (813 / 32000) (526046361413 / 500000000000) (526062800619 / 500000000000) (3305246081 / 1000000000) (413168803 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (13 / 512) (813 / 32000) (3305246081 / 1000000000) (413168803 / 125000000) (49375743 / 1000000000000) (49391203 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3305246081 / 1000000000) (413168803 / 125000000) (464608241 / 250000000) (464617331 / 250000000) (49375743 / 1000000000000) (49391203 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0377 :
    ∀ t ∈ Set.Icc ((813 / 32000) : ℝ) (1627 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1052125601237 / 1000000000000) : ℝ) ≤ Real.exp (2 * (813 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (813 / 32000)) (1052125601237 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1627 / 64000) : ℝ)) ≤ (1052158480677 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1627 / 64000)) (1052158480677 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((464617239 / 250000000) : ℝ) ≤ Real.exp (3 * (3305349371 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3305349371 / 1000000000) / 16) (464617239 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1652726859 / 500000000) : ℝ) / 16) ≤ (929252659 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1652726859 / 500000000) / 16) (929252659 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((813 / 32000) : ℝ) (1627 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3305349371 / 1000000000) (1652726859 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (813 / 32000) (1627 / 64000) (1052125601237 / 1000000000000) (1052158480677 / 1000000000000) (3305349371 / 1000000000) (1652726859 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (813 / 32000) (1627 / 64000) (3305349371 / 1000000000) (1652726859 / 500000000) (9872089 / 200000000000) (493759 / 10000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3305349371 / 1000000000) (1652726859 / 500000000) (464617239 / 250000000) (929252659 / 500000000) (9872089 / 200000000000) (493759 / 10000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0378 :
    ∀ t ∈ Set.Icc ((1627 / 64000) : ℝ) (407 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((263039620169 / 250000000000) : ℝ) ≤ Real.exp (2 * (1627 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1627 / 64000)) (263039620169 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((407 / 16000) : ℝ)) ≤ (1052191361143 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (407 / 16000)) (1052191361143 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((37170099 / 20000000) : ℝ) ≤ Real.exp (3 * (661090533 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (661090533 / 200000000) / 16) (37170099 / 20000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((661111403 / 200000000) : ℝ) / 16) ≤ (371708263 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (661111403 / 200000000) / 16) (371708263 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1627 / 64000) : ℝ) (407 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (661090533 / 200000000) (661111403 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1627 / 64000) (407 / 16000) (263039620169 / 250000000000) (1052191361143 / 1000000000000) (661090533 / 200000000) (661111403 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1627 / 64000) (407 / 16000) (661090533 / 200000000) (661111403 / 200000000) (49345151 / 1000000000000) (24680301 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (661090533 / 200000000) (661111403 / 200000000) (37170099 / 20000000) (371708263 / 200000000) (49345151 / 1000000000000) (24680301 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0379 :
    ∀ t ∈ Set.Icc ((407 / 16000) : ℝ) (1629 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((526095680571 / 500000000000) : ℝ) ≤ Real.exp (2 * (407 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (407 / 16000)) (526095680571 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1629 / 64000) : ℝ)) ≤ (1052224242637 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1629 / 64000)) (1052224242637 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1858540947 / 1000000000) : ℝ) ≤ Real.exp (3 * (1652777981 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1652777981 / 500000000) / 16) (1858540947 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((826415079 / 250000000) : ℝ) / 16) ≤ (1858577313 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (826415079 / 250000000) / 16) (1858577313 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((407 / 16000) : ℝ) (1629 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1652777981 / 500000000) (826415079 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (407 / 16000) (1629 / 64000) (526095680571 / 500000000000) (1052224242637 / 1000000000000) (1652777981 / 500000000) (826415079 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (407 / 16000) (1629 / 64000) (1652777981 / 500000000) (826415079 / 250000000) (49329861 / 1000000000000) (12336327 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1652777981 / 500000000) (826415079 / 250000000) (1858540947 / 1000000000) (1858577313 / 1000000000) (49329861 / 1000000000000) (12336327 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch018 :
    ∀ t ∈ Set.Icc ((1609 / 64000) : ℝ) (1629 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0360
      hpThetaDensityTwoTermCompact_cell0361)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0362
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0363
      hpThetaDensityTwoTermCompact_cell0364)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0365
      hpThetaDensityTwoTermCompact_cell0366)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0367
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0368
      hpThetaDensityTwoTermCompact_cell0369))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0370
      hpThetaDensityTwoTermCompact_cell0371)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0372
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0373
      hpThetaDensityTwoTermCompact_cell0374)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0375
      hpThetaDensityTwoTermCompact_cell0376)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0377
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0378
      hpThetaDensityTwoTermCompact_cell0379)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch018
end HodgeProofHP
