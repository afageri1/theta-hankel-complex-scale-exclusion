/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0240 :
    ∀ t ∈ Set.Icc ((1489 / 64000) : ℝ) (149 / 6400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((52381540851 / 50000000000) : ℝ) ≤ Real.exp (2 * (1489 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1489 / 64000)) (52381540851 / 50000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((149 / 6400) : ℝ)) ≤ (209532711199 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (149 / 6400)) (209532711199 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((115847181 / 62500000) : ℝ) ≤ Real.exp (3 * (3291228593 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3291228593 / 1000000000) / 16) (115847181 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1645666247 / 500000000) : ℝ) / 16) ≤ (57924719 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1645666247 / 500000000) / 16) (57924719 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1489 / 64000) : ℝ) (149 / 6400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3291228593 / 1000000000) (1645666247 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1489 / 64000) (149 / 6400) (52381540851 / 50000000000) (209532711199 / 200000000000) (3291228593 / 1000000000) (1645666247 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1489 / 64000) (149 / 6400) (3291228593 / 1000000000) (1645666247 / 500000000) (2574823 / 50000000000) (10302503 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3291228593 / 1000000000) (1645666247 / 500000000) (115847181 / 62500000) (57924719 / 31250000) (2574823 / 50000000000) (10302503 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0241 :
    ∀ t ∈ Set.Icc ((149 / 6400) : ℝ) (1491 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((523831777997 / 500000000000) : ℝ) ≤ Real.exp (2 * (149 / 6400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (149 / 6400)) (523831777997 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1491 / 64000) : ℝ)) ≤ (1047696295993 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1491 / 64000)) (1047696295993 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1853590643 / 1000000000) : ℝ) ≤ Real.exp (3 * (1645665723 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1645665723 / 500000000) / 16) (1853590643 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((65828707 / 20000000) : ℝ) / 16) ≤ (463406689 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (65828707 / 20000000) / 16) (463406689 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((149 / 6400) : ℝ) (1491 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1645665723 / 500000000) (65828707 / 20000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (149 / 6400) (1491 / 64000) (523831777997 / 500000000000) (1047696295993 / 1000000000000) (1645665723 / 500000000) (65828707 / 20000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (149 / 6400) (1491 / 64000) (1645665723 / 500000000) (65828707 / 20000000) (12870143 / 250000000000) (51496623 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1645665723 / 500000000) (65828707 / 20000000) (1853590643 / 1000000000) (463406689 / 250000000) (12870143 / 250000000000) (51496623 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0242 :
    ∀ t ∈ Set.Icc ((1491 / 64000) : ℝ) (373 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((130962036999 / 125000000000) : ℝ) ≤ Real.exp (2 * (1491 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1491 / 64000)) (130962036999 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((373 / 16000) : ℝ)) ≤ (523864518507 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (373 / 16000)) (523864518507 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((185362639 / 100000000) : ℝ) ≤ Real.exp (3 * (3291434301 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3291434301 / 1000000000) / 16) (185362639 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3291538209 / 1000000000) : ℝ) / 16) ≤ (370732501 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3291538209 / 1000000000) / 16) (370732501 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1491 / 64000) : ℝ) (373 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3291434301 / 1000000000) (3291538209 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1491 / 64000) (373 / 16000) (130962036999 / 125000000000) (523864518507 / 500000000000) (3291434301 / 1000000000) (3291538209 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1491 / 64000) (373 / 16000) (3291434301 / 1000000000) (3291538209 / 1000000000) (51464689 / 1000000000000) (10296147 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3291434301 / 1000000000) (3291538209 / 1000000000) (185362639 / 100000000) (370732501 / 200000000) (51464689 / 1000000000000) (10296147 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0243 :
    ∀ t ∈ Set.Icc ((373 / 16000) : ℝ) (1493 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1047729037013 / 1000000000000) : ℝ) ≤ Real.exp (2 * (373 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (373 / 16000)) (1047729037013 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1493 / 64000) : ℝ)) ≤ (523880889529 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1493 / 64000)) (523880889529 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1853662139 / 1000000000) : ℝ) ≤ Real.exp (3 * (82288429 / 25000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (82288429 / 25000000) / 16) (1853662139 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3291641071 / 1000000000) : ℝ) / 16) ≤ (115856141 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3291641071 / 1000000000) / 16) (115856141 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((373 / 16000) : ℝ) (1493 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (82288429 / 25000000) (3291641071 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (373 / 16000) (1493 / 64000) (1047729037013 / 1000000000000) (523880889529 / 500000000000) (82288429 / 25000000) (3291641071 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (373 / 16000) (1493 / 64000) (82288429 / 25000000) (3291641071 / 1000000000) (5144881 / 100000000000) (12866213 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (82288429 / 25000000) (3291641071 / 1000000000) (1853662139 / 1000000000) (115856141 / 62500000) (5144881 / 100000000000) (12866213 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0244 :
    ∀ t ∈ Set.Icc ((1493 / 64000) : ℝ) (747 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1047761779057 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1493 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1493 / 64000)) (1047761779057 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((747 / 32000) : ℝ)) ≤ (8382356177 / 8000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (747 / 32000)) (8382356177 / 8000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1853697891 / 1000000000) : ℝ) ≤ Real.exp (3 * (1645820011 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1645820011 / 500000000) / 16) (1853697891 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3291743937 / 1000000000) : ℝ) / 16) ≤ (185373401 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3291743937 / 1000000000) / 16) (185373401 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1493 / 64000) : ℝ) (747 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1645820011 / 500000000) (3291743937 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1493 / 64000) (747 / 32000) (1047761779057 / 1000000000000) (8382356177 / 8000000000) (1645820011 / 500000000) (3291743937 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1493 / 64000) (747 / 32000) (1645820011 / 500000000) (3291743937 / 1000000000) (10286587 / 200000000000) (51448973 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1645820011 / 500000000) (3291743937 / 1000000000) (1853697891 / 1000000000) (185373401 / 100000000) (10286587 / 200000000000) (51448973 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0245 :
    ∀ t ∈ Set.Icc ((747 / 32000) : ℝ) (299 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((261948630531 / 250000000000) : ℝ) ≤ Real.exp (2 * (747 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (747 / 32000)) (261948630531 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((299 / 12800) : ℝ)) ≤ (209565453243 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (299 / 12800)) (209565453243 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((463433411 / 250000000) : ℝ) ≤ Real.exp (3 * (411467861 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (411467861 / 125000000) / 16) (463433411 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((658369361 / 200000000) : ℝ) / 16) ≤ (463442441 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (658369361 / 200000000) / 16) (463442441 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((747 / 32000) : ℝ) (299 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (411467861 / 125000000) (658369361 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (747 / 32000) (299 / 12800) (261948630531 / 250000000000) (209565453243 / 200000000000) (411467861 / 125000000) (658369361 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (747 / 32000) (299 / 12800) (411467861 / 125000000) (658369361 / 200000000) (25708533 / 500000000000) (51433099 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (411467861 / 125000000) (658369361 / 200000000) (463433411 / 250000000) (463442441 / 250000000) (25708533 / 500000000000) (51433099 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0246 :
    ∀ t ∈ Set.Icc ((299 / 12800) : ℝ) (187 / 8000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((523913633107 / 500000000000) : ℝ) ≤ Real.exp (2 * (299 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (299 / 12800)) (523913633107 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((187 / 8000) : ℝ)) ≤ (1047860011329 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (187 / 8000)) (1047860011329 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1853769399 / 1000000000) : ℝ) ≤ Real.exp (3 * (822961439 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (822961439 / 250000000) / 16) (1853769399 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3291949677 / 1000000000) : ℝ) / 16) ≤ (1853805521 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3291949677 / 1000000000) / 16) (1853805521 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((299 / 12800) : ℝ) (187 / 8000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (822961439 / 250000000) (3291949677 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (299 / 12800) (187 / 8000) (523913633107 / 500000000000) (1047860011329 / 1000000000000) (822961439 / 250000000) (3291949677 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (299 / 12800) (187 / 8000) (822961439 / 250000000) (3291949677 / 1000000000) (128503 / 2500000000) (51417229 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (822961439 / 250000000) (3291949677 / 1000000000) (1853769399 / 1000000000) (1853805521 / 1000000000) (128503 / 2500000000) (51417229 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0247 :
    ∀ t ∈ Set.Icc ((187 / 8000) : ℝ) (1497 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((16372812677 / 15625000000) : ℝ) ≤ Real.exp (2 * (187 / 8000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (187 / 8000)) (16372812677 / 15625000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1497 / 64000) : ℝ)) ≤ (523946378733 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1497 / 64000)) (523946378733 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((370761031 / 200000000) : ℝ) ≤ Real.exp (3 * (822987157 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (822987157 / 250000000) / 16) (370761031 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((411506569 / 125000000) : ℝ) / 16) ≤ (2896627 / 1562500) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (411506569 / 125000000) / 16) (2896627 / 1562500) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((187 / 8000) : ℝ) (1497 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (822987157 / 250000000) (411506569 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (187 / 8000) (1497 / 64000) (16372812677 / 15625000000) (523946378733 / 500000000000) (822987157 / 250000000) (411506569 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (187 / 8000) (1497 / 64000) (822987157 / 250000000) (411506569 / 125000000) (25692669 / 500000000000) (51401363 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (822987157 / 250000000) (411506569 / 125000000) (370761031 / 200000000) (2896627 / 1562500) (25692669 / 500000000000) (51401363 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0248 :
    ∀ t ∈ Set.Icc ((1497 / 64000) : ℝ) (749 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((209578551493 / 200000000000) : ℝ) ≤ Real.exp (2 * (1497 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1497 / 64000)) (209578551493 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((749 / 32000) : ℝ)) ≤ (523962752313 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (749 / 32000)) (523962752313 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((926920457 / 500000000) : ℝ) ≤ Real.exp (3 * (3292051503 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3292051503 / 1000000000) / 16) (926920457 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((329215543 / 100000000) : ℝ) / 16) ≤ (23173463 / 12500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (329215543 / 100000000) / 16) (23173463 / 12500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1497 / 64000) : ℝ) (749 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3292051503 / 1000000000) (329215543 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1497 / 64000) (749 / 32000) (209578551493 / 200000000000) (523962752313 / 500000000000) (3292051503 / 1000000000) (329215543 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1497 / 64000) (749 / 32000) (3292051503 / 1000000000) (329215543 / 100000000) (25684741 / 500000000000) (25692751 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3292051503 / 1000000000) (329215543 / 100000000) (926920457 / 500000000) (23173463 / 12500000) (25684741 / 500000000000) (25692751 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0249 :
    ∀ t ∈ Set.Icc ((749 / 32000) : ℝ) (1499 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((8383404037 / 8000000000) : ℝ) ≤ Real.exp (2 * (749 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (749 / 32000)) (8383404037 / 8000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1499 / 64000) : ℝ)) ≤ (104795825281 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1499 / 64000)) (104795825281 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((926938337 / 500000000) : ℝ) ≤ Real.exp (3 * (3292154381 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3292154381 / 1000000000) / 16) (926938337 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((411532289 / 125000000) : ℝ) / 16) ≤ (926956401 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (411532289 / 125000000) / 16) (926956401 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((749 / 32000) : ℝ) (1499 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3292154381 / 1000000000) (411532289 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (749 / 32000) (1499 / 64000) (8383404037 / 8000000000) (104795825281 / 100000000000) (3292154381 / 1000000000) (411532289 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (749 / 32000) (1499 / 64000) (3292154381 / 1000000000) (411532289 / 125000000) (51353629 / 1000000000000) (10273929 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3292154381 / 1000000000) (411532289 / 125000000) (926938337 / 500000000) (926956401 / 500000000) (51353629 / 1000000000000) (10273929 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0250 :
    ∀ t ∈ Set.Icc ((1499 / 64000) : ℝ) (3 / 128), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1047958252809 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1499 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1499 / 64000)) (1047958252809 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3 / 128) : ℝ)) ≤ (1047991002017 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3 / 128)) (1047991002017 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1853912437 / 1000000000) : ℝ) ≤ Real.exp (3 * (3292257263 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3292257263 / 1000000000) / 16) (1853912437 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((823090299 / 250000000) : ℝ) / 16) ≤ (926974283 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (823090299 / 250000000) / 16) (926974283 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1499 / 64000) : ℝ) (3 / 128),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3292257263 / 1000000000) (823090299 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1499 / 64000) (3 / 128) (1047958252809 / 1000000000000) (1047991002017 / 1000000000000) (3292257263 / 1000000000) (823090299 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1499 / 64000) (3 / 128) (3292257263 / 1000000000) (823090299 / 250000000) (51337781 / 1000000000000) (802403 / 15625000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3292257263 / 1000000000) (823090299 / 250000000) (1853912437 / 1000000000) (926974283 / 500000000) (51337781 / 1000000000000) (802403 / 15625000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0251 :
    ∀ t ∈ Set.Icc ((3 / 128) : ℝ) (1501 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((32749718813 / 31250000000) : ℝ) ≤ Real.exp (2 * (3 / 128)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3 / 128)) (32749718813 / 31250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1501 / 64000) : ℝ)) ≤ (131002969031 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1501 / 64000)) (131002969031 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1853948201 / 1000000000) : ℝ) ≤ Real.exp (3 * (823090037 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (823090037 / 250000000) / 16) (1853948201 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((823116021 / 250000000) : ℝ) / 16) ≤ (463496083 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (823116021 / 250000000) / 16) (463496083 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3 / 128) : ℝ) (1501 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (823090037 / 250000000) (823116021 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3 / 128) (1501 / 64000) (32749718813 / 31250000000) (131002969031 / 125000000000) (823090037 / 250000000) (823116021 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3 / 128) (1501 / 64000) (823090037 / 250000000) (823116021 / 250000000) (51321937 / 1000000000000) (6417243 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (823090037 / 250000000) (823116021 / 250000000) (1853948201 / 1000000000) (463496083 / 250000000) (51321937 / 1000000000000) (6417243 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0252 :
    ∀ t ∈ Set.Icc ((1501 / 64000) : ℝ) (751 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1048023752247 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1501 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1501 / 64000)) (1048023752247 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((751 / 32000) : ℝ)) ≤ (524028251751 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (751 / 32000)) (524028251751 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((926991983 / 500000000) : ℝ) ≤ Real.exp (3 * (658492607 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (658492607 / 200000000) / 16) (926991983 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((51446359 / 15625000) : ℝ) / 16) ≤ (18540201 / 10000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (51446359 / 15625000) / 16) (18540201 / 10000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1501 / 64000) : ℝ) (751 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (658492607 / 200000000) (51446359 / 15625000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1501 / 64000) (751 / 32000) (1048023752247 / 1000000000000) (524028251751 / 500000000000) (658492607 / 200000000) (51446359 / 15625000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1501 / 64000) (751 / 32000) (658492607 / 200000000) (51446359 / 15625000) (25653049 / 500000000000) (513221 / 10000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (658492607 / 200000000) (51446359 / 15625000) (926991983 / 500000000) (18540201 / 10000000) (25653049 / 500000000000) (513221 / 10000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0253 :
    ∀ t ∈ Set.Icc ((751 / 32000) : ℝ) (1503 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1048056503501 / 1000000000000) : ℝ) ≤ Real.exp (2 * (751 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (751 / 32000)) (1048056503501 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1503 / 64000) : ℝ)) ≤ (1048089255779 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1503 / 64000)) (1048089255779 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((927009867 / 500000000) : ℝ) ≤ Real.exp (3 * (1646282963 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1646282963 / 500000000) / 16) (927009867 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((329266987 / 100000000) : ℝ) / 16) ≤ (1854055869 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (329266987 / 100000000) / 16) (1854055869 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((751 / 32000) : ℝ) (1503 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1646282963 / 500000000) (329266987 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (751 / 32000) (1503 / 64000) (1048056503501 / 1000000000000) (1048089255779 / 1000000000000) (1646282963 / 500000000) (329266987 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (751 / 32000) (1503 / 64000) (1646282963 / 500000000) (329266987 / 100000000) (51290263 / 1000000000000) (51306261 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1646282963 / 500000000) (329266987 / 100000000) (927009867 / 500000000) (1854055869 / 1000000000) (51290263 / 1000000000000) (51306261 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0254 :
    ∀ t ∈ Set.Icc ((1503 / 64000) : ℝ) (47 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((524044627889 / 500000000000) : ℝ) ≤ Real.exp (2 * (1503 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1503 / 64000)) (524044627889 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((47 / 2000) : ℝ)) ≤ (26203050227 / 25000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (47 / 2000)) (26203050227 / 25000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1854055503 / 1000000000) : ℝ) ≤ Real.exp (3 * (3292668821 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3292668821 / 1000000000) / 16) (1854055503 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3292772767 / 1000000000) : ℝ) / 16) ≤ (46352291 / 25000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3292772767 / 1000000000) / 16) (46352291 / 25000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1503 / 64000) : ℝ) (47 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3292668821 / 1000000000) (3292772767 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1503 / 64000) (47 / 2000) (524044627889 / 500000000000) (26203050227 / 25000000000) (3292668821 / 1000000000) (3292772767 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1503 / 64000) (47 / 2000) (3292668821 / 1000000000) (3292772767 / 1000000000) (51274433 / 1000000000000) (25645213 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3292668821 / 1000000000) (3292772767 / 1000000000) (1854055503 / 1000000000) (46352291 / 25000000) (51274433 / 1000000000000) (25645213 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0255 :
    ∀ t ∈ Set.Icc ((47 / 2000) : ℝ) (301 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1048122009079 / 1000000000000) : ℝ) ≤ Real.exp (2 * (47 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (47 / 2000)) (1048122009079 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((301 / 12800) : ℝ)) ≤ (209630952681 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (301 / 12800)) (209630952681 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((927045637 / 500000000) : ℝ) ≤ Real.exp (3 * (1646385859 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1646385859 / 500000000) / 16) (927045637 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((823218917 / 250000000) : ℝ) / 16) ≤ (1854127413 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (823218917 / 250000000) / 16) (1854127413 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((47 / 2000) : ℝ) (301 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1646385859 / 500000000) (823218917 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (47 / 2000) (301 / 12800) (1048122009079 / 1000000000000) (209630952681 / 200000000000) (1646385859 / 500000000) (823218917 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (47 / 2000) (301 / 12800) (1646385859 / 500000000) (823218917 / 250000000) (51258607 / 1000000000000) (12818649 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1646385859 / 500000000) (823218917 / 250000000) (927045637 / 500000000) (1854127413 / 1000000000) (51258607 / 1000000000000) (12818649 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0256 :
    ∀ t ∈ Set.Icc ((301 / 12800) : ℝ) (753 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((262038690851 / 250000000000) : ℝ) ≤ Real.exp (2 * (301 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (301 / 12800)) (262038690851 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((753 / 32000) : ℝ)) ≤ (1048187518753 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (753 / 32000)) (1048187518753 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1854127047 / 1000000000) : ℝ) ≤ Real.exp (3 * (3292874619 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3292874619 / 1000000000) / 16) (1854127047 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((823244643 / 250000000) : ℝ) / 16) ≤ (463540797 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (823244643 / 250000000) / 16) (463540797 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((301 / 12800) : ℝ) (753 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3292874619 / 1000000000) (823244643 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (301 / 12800) (753 / 32000) (262038690851 / 250000000000) (1048187518753 / 1000000000000) (3292874619 / 1000000000) (823244643 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (301 / 12800) (753 / 32000) (3292874619 / 1000000000) (823244643 / 250000000) (10248557 / 200000000000) (5125877 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3292874619 / 1000000000) (823244643 / 250000000) (1854127047 / 1000000000) (463540797 / 250000000) (10248557 / 200000000000) (5125877 / 100000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0257 :
    ∀ t ∈ Set.Icc ((753 / 32000) : ℝ) (1507 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((32755859961 / 31250000000) : ℝ) ≤ Real.exp (2 * (753 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (753 / 32000)) (32755859961 / 31250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1507 / 64000) : ℝ)) ≤ (8385762201 / 8000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1507 / 64000)) (8385762201 / 8000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((927081411 / 500000000) : ℝ) ≤ Real.exp (3 * (3292977523 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3292977523 / 1000000000) / 16) (927081411 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3293081479 / 1000000000) : ℝ) / 16) ≤ (463549741 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3293081479 / 1000000000) / 16) (463549741 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((753 / 32000) : ℝ) (1507 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3292977523 / 1000000000) (3293081479 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (753 / 32000) (1507 / 64000) (32755859961 / 31250000000) (8385762201 / 8000000000) (3292977523 / 1000000000) (3293081479 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (753 / 32000) (1507 / 64000) (3292977523 / 1000000000) (3293081479 / 1000000000) (6403371 / 125000000000) (12810737 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3292977523 / 1000000000) (3293081479 / 1000000000) (927081411 / 500000000) (463549741 / 250000000) (6403371 / 125000000000) (12810737 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0258 :
    ∀ t ∈ Set.Icc ((1507 / 64000) : ℝ) (377 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((262055068781 / 250000000000) : ℝ) ≤ Real.exp (2 * (1507 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1507 / 64000)) (262055068781 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((377 / 16000) : ℝ)) ≤ (26206325813 / 25000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (377 / 16000)) (26206325813 / 25000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1854198599 / 1000000000) : ℝ) ≤ Real.exp (3 * (329308043 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (329308043 / 100000000) / 16) (1854198599 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((329318439 / 100000000) : ℝ) / 16) ≤ (1854234743 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (329318439 / 100000000) / 16) (1854234743 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1507 / 64000) : ℝ) (377 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (329308043 / 100000000) (329318439 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1507 / 64000) (377 / 16000) (262055068781 / 250000000000) (26206325813 / 25000000000) (329308043 / 100000000) (329318439 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1507 / 64000) (377 / 16000) (329308043 / 100000000) (329318439 / 100000000) (10242231 / 200000000000) (5122713 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (329308043 / 100000000) (329318439 / 100000000) (1854198599 / 1000000000) (1854234743 / 1000000000) (10242231 / 200000000000) (5122713 / 100000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0259 :
    ∀ t ∈ Set.Icc ((377 / 16000) : ℝ) (1509 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1048253032519 / 1000000000000) : ℝ) ≤ Real.exp (2 * (377 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (377 / 16000)) (1048253032519 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1509 / 64000) : ℝ)) ≤ (1048285790939 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1509 / 64000)) (1048285790939 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1854234377 / 1000000000) : ℝ) ≤ Real.exp (3 * (164659167 / 50000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (164659167 / 50000000) / 16) (1854234377 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3293287303 / 1000000000) : ℝ) / 16) ≤ (1854270523 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3293287303 / 1000000000) / 16) (1854270523 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((377 / 16000) : ℝ) (1509 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (164659167 / 50000000) (3293287303 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (377 / 16000) (1509 / 64000) (1048253032519 / 1000000000000) (1048285790939 / 1000000000000) (164659167 / 50000000) (3293287303 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (377 / 16000) (1509 / 64000) (164659167 / 50000000) (3293287303 / 1000000000) (25597673 / 500000000000) (51211317 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (164659167 / 50000000) (3293287303 / 1000000000) (1854234377 / 1000000000) (1854270523 / 1000000000) (25597673 / 500000000000) (51211317 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch012 :
    ∀ t ∈ Set.Icc ((1489 / 64000) : ℝ) (1509 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0240
      hpThetaDensityTwoTermCompact_cell0241)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0242
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0243
      hpThetaDensityTwoTermCompact_cell0244)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0245
      hpThetaDensityTwoTermCompact_cell0246)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0247
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0248
      hpThetaDensityTwoTermCompact_cell0249))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0250
      hpThetaDensityTwoTermCompact_cell0251)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0252
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0253
      hpThetaDensityTwoTermCompact_cell0254)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0255
      hpThetaDensityTwoTermCompact_cell0256)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0257
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0258
      hpThetaDensityTwoTermCompact_cell0259)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch012
end HodgeProofHP
