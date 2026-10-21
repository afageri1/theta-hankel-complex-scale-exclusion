/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0100 :
    ∀ t ∈ Set.Icc ((1349 / 64000) : ℝ) (27 / 1280), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((32595545117 / 31250000000) : ℝ) ≤ Real.exp (2 * (1349 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1349 / 64000)) (32595545117 / 31250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((27 / 1280) : ℝ)) ≤ (1043090039799 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (27 / 1280)) (1043090039799 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1848568253 / 1000000000) : ℝ) ≤ Real.exp (3 * (81921523 / 25000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (81921523 / 25000000) / 16) (1848568253 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((204810273 / 62500000) : ℝ) / 16) ≤ (184860411 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (204810273 / 62500000) / 16) (184860411 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1349 / 64000) : ℝ) (27 / 1280),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (81921523 / 25000000) (204810273 / 62500000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1349 / 64000) (27 / 1280) (32595545117 / 31250000000) (1043090039799 / 1000000000000) (81921523 / 25000000) (204810273 / 62500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1349 / 64000) (27 / 1280) (81921523 / 25000000) (204810273 / 62500000) (53764717 / 1000000000000) (53781407 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (81921523 / 25000000) (204810273 / 62500000) (1848568253 / 1000000000) (184860411 / 100000000) (53764717 / 1000000000000) (53781407 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0101 :
    ∀ t ∈ Set.Icc ((27 / 1280) : ℝ) (1351 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((521545019899 / 500000000000) : ℝ) ≤ Real.exp (2 * (27 / 1280)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (27 / 1280)) (521545019899 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1351 / 64000) : ℝ)) ≤ (130390329609 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1351 / 64000)) (130390329609 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1848603747 / 1000000000) : ℝ) ≤ Real.exp (3 * (819240831 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (819240831 / 250000000) / 16) (1848603747 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((131082671 / 40000000) : ℝ) / 16) ≤ (924319803 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (131082671 / 40000000) / 16) (924319803 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((27 / 1280) : ℝ) (1351 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (819240831 / 250000000) (131082671 / 40000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (27 / 1280) (1351 / 64000) (521545019899 / 500000000000) (130390329609 / 125000000000) (819240831 / 250000000) (131082671 / 40000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (27 / 1280) (1351 / 64000) (819240831 / 250000000) (131082671 / 40000000) (26874101 / 500000000000) (53764887 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (819240831 / 250000000) (131082671 / 40000000) (1848603747 / 1000000000) (924319803 / 500000000) (26874101 / 500000000000) (53764887 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0102 :
    ∀ t ∈ Set.Icc ((1351 / 64000) : ℝ) (169 / 8000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1043122636871 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1351 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1351 / 64000)) (1043122636871 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((169 / 8000) : ℝ)) ≤ (260788808741 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (169 / 8000)) (260788808741 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1848639243 / 1000000000) : ℝ) ≤ Real.exp (3 * (3277065731 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3277065731 / 1000000000) / 16) (1848639243 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((655433837 / 200000000) : ℝ) / 16) ≤ (57771097 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (655433837 / 200000000) / 16) (57771097 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1351 / 64000) : ℝ) (169 / 8000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3277065731 / 1000000000) (655433837 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1351 / 64000) (169 / 8000) (1043122636871 / 1000000000000) (260788808741 / 250000000000) (3277065731 / 1000000000) (655433837 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1351 / 64000) (169 / 8000) (3277065731 / 1000000000) (655433837 / 200000000) (13432923 / 250000000000) (13437093 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3277065731 / 1000000000) (655433837 / 200000000) (1848639243 / 1000000000) (57771097 / 31250000) (13432923 / 250000000000) (13437093 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0103 :
    ∀ t ∈ Set.Icc ((169 / 8000) : ℝ) (1353 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1043155234963 / 1000000000000) : ℝ) ≤ Real.exp (2 * (169 / 8000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (169 / 8000)) (1043155234963 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1353 / 64000) : ℝ)) ≤ (41727513363 / 40000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1353 / 64000)) (41727513363 / 40000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1848674741 / 1000000000) : ℝ) ≤ Real.exp (3 * (163858407 / 50000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (163858407 / 50000000) / 16) (1848674741 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1638635799 / 500000000) : ℝ) / 16) ≤ (1848710603 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1638635799 / 500000000) / 16) (1848710603 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((169 / 8000) : ℝ) (1353 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (163858407 / 50000000) (1638635799 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (169 / 8000) (1353 / 64000) (1043155234963 / 1000000000000) (41727513363 / 40000000000) (163858407 / 50000000) (1638635799 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (169 / 8000) (1353 / 64000) (163858407 / 50000000) (1638635799 / 500000000) (26857593 / 500000000000) (53731861 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (163858407 / 50000000) (1638635799 / 500000000) (1848674741 / 1000000000) (1848710603 / 1000000000) (26857593 / 500000000000) (53731861 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0104 :
    ∀ t ∈ Set.Icc ((1353 / 64000) : ℝ) (677 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((521593917037 / 500000000000) : ℝ) ≤ Real.exp (2 * (1353 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1353 / 64000)) (521593917037 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((677 / 32000) : ℝ)) ≤ (260805108551 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (677 / 32000)) (260805108551 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((11554439 / 6250000) : ℝ) ≤ Real.exp (3 * (1638635277 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1638635277 / 500000000) / 16) (11554439 / 6250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1638687007 / 500000000) : ℝ) / 16) ≤ (231093263 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1638687007 / 500000000) / 16) (231093263 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1353 / 64000) : ℝ) (677 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1638635277 / 500000000) (1638687007 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1353 / 64000) (677 / 32000) (521593917037 / 500000000000) (260805108551 / 250000000000) (1638635277 / 500000000) (1638687007 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1353 / 64000) (677 / 32000) (1638635277 / 500000000) (1638687007 / 500000000) (10739737 / 200000000000) (13428839 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1638635277 / 500000000) (1638687007 / 500000000) (11554439 / 6250000) (231093263 / 125000000) (10739737 / 200000000000) (13428839 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0105 :
    ∀ t ∈ Set.Icc ((677 / 32000) : ℝ) (271 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1043220434203 / 1000000000000) : ℝ) ≤ Real.exp (2 * (677 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (677 / 32000)) (1043220434203 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((271 / 12800) : ℝ)) ≤ (130406629419 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (271 / 12800)) (130406629419 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((924372871 / 500000000) : ℝ) ≤ Real.exp (3 * (327737297 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (327737297 / 100000000) / 16) (924372871 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1638738217 / 500000000) : ℝ) / 16) ≤ (231097701 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1638738217 / 500000000) / 16) (231097701 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((677 / 32000) : ℝ) (271 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (327737297 / 100000000) (1638738217 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (677 / 32000) (271 / 12800) (1043220434203 / 1000000000000) (130406629419 / 125000000000) (327737297 / 100000000) (1638738217 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (677 / 32000) (271 / 12800) (327737297 / 100000000) (1638738217 / 500000000) (53682187 / 1000000000000) (26849427 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (327737297 / 100000000) (1638738217 / 500000000) (924372871 / 500000000) (231097701 / 125000000) (53682187 / 1000000000000) (26849427 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0106 :
    ∀ t ∈ Set.Icc ((271 / 12800) : ℝ) (339 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1043253035351 / 1000000000000) : ℝ) ≤ Real.exp (2 * (271 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (271 / 12800)) (1043253035351 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((339 / 16000) : ℝ)) ≤ (521642818759 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (339 / 16000)) (521642818759 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((462195311 / 250000000) : ℝ) ≤ Real.exp (3 * (3277475389 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3277475389 / 1000000000) / 16) (462195311 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((409697357 / 125000000) : ℝ) / 16) ≤ (231102139 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (409697357 / 125000000) / 16) (231102139 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((271 / 12800) : ℝ) (339 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3277475389 / 1000000000) (409697357 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (271 / 12800) (339 / 16000) (1043253035351 / 1000000000000) (521642818759 / 500000000000) (3277475389 / 1000000000) (409697357 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (271 / 12800) (339 / 16000) (3277475389 / 1000000000) (409697357 / 125000000) (10733139 / 200000000000) (53682357 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3277475389 / 1000000000) (409697357 / 125000000) (462195311 / 250000000) (231102139 / 125000000) (10733139 / 200000000000) (53682357 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0107 :
    ∀ t ∈ Set.Icc ((339 / 16000) : ℝ) (1357 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1043285637517 / 1000000000000) : ℝ) ≤ Real.exp (2 * (339 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (339 / 16000)) (1043285637517 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1357 / 64000) : ℝ)) ≤ (16301847511 / 15625000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1357 / 64000)) (16301847511 / 15625000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1848816749 / 1000000000) : ℝ) ≤ Real.exp (3 * (819394453 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (819394453 / 250000000) / 16) (1848816749 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1638840641 / 500000000) : ℝ) / 16) ≤ (1848852619 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1638840641 / 500000000) / 16) (1848852619 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((339 / 16000) : ℝ) (1357 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (819394453 / 250000000) (1638840641 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (339 / 16000) (1357 / 64000) (1043285637517 / 1000000000000) (16301847511 / 15625000000) (819394453 / 250000000) (1638840641 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (339 / 16000) (1357 / 64000) (819394453 / 250000000) (1638840641 / 500000000) (53649207 / 1000000000000) (10733173 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (819394453 / 250000000) (1638840641 / 500000000) (1848816749 / 1000000000) (1848852619 / 1000000000) (53649207 / 1000000000000) (10733173 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0108 :
    ∀ t ∈ Set.Icc ((1357 / 64000) : ℝ) (679 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1043318240703 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1357 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1357 / 64000)) (1043318240703 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((679 / 32000) : ℝ)) ≤ (1043350844909 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (679 / 32000)) (1043350844909 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((57776633 / 31250000) : ℝ) ≤ Real.exp (3 * (1638840119 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1638840119 / 500000000) / 16) (57776633 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3277783711 / 1000000000) : ℝ) / 16) ≤ (1848888127 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3277783711 / 1000000000) / 16) (1848888127 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1357 / 64000) : ℝ) (679 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1638840119 / 500000000) (3277783711 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1357 / 64000) (679 / 32000) (1043318240703 / 1000000000000) (1043350844909 / 1000000000000) (1638840119 / 500000000) (3277783711 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1357 / 64000) (679 / 32000) (1638840119 / 500000000) (3277783711 / 1000000000) (13408181 / 250000000000) (53649377 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1638840119 / 500000000) (3277783711 / 1000000000) (57776633 / 31250000) (1848888127 / 1000000000) (13408181 / 250000000000) (53649377 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0109 :
    ∀ t ∈ Set.Icc ((679 / 32000) : ℝ) (1359 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((260837711227 / 250000000000) : ℝ) ≤ Real.exp (2 * (679 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (679 / 32000)) (260837711227 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1359 / 64000) : ℝ)) ≤ (260845862533 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1359 / 64000)) (260845862533 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((462221941 / 250000000) : ℝ) ≤ Real.exp (3 * (3277782667 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3277782667 / 1000000000) / 16) (462221941 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((51216971 / 15625000) : ℝ) / 16) ≤ (924461819 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (51216971 / 15625000) / 16) (924461819 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((679 / 32000) : ℝ) (1359 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3277782667 / 1000000000) (51216971 / 15625000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (679 / 32000) (1359 / 64000) (260837711227 / 250000000000) (260845862533 / 250000000000) (3277782667 / 1000000000) (51216971 / 15625000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (679 / 32000) (1359 / 64000) (3277782667 / 1000000000) (51216971 / 15625000) (10723249 / 200000000000) (26816447 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3277782667 / 1000000000) (51216971 / 15625000) (462221941 / 250000000) (924461819 / 500000000) (10723249 / 200000000000) (26816447 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0110 :
    ∀ t ∈ Set.Icc ((1359 / 64000) : ℝ) (17 / 800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1043383450131 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1359 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1359 / 64000)) (1043383450131 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((17 / 800) : ℝ)) ≤ (521708028187 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (17 / 800)) (521708028187 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((924461637 / 500000000) : ℝ) ≤ Real.exp (3 * (3277885099 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3277885099 / 1000000000) / 16) (924461637 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3277988579 / 1000000000) : ℝ) / 16) ≤ (1848959149 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3277988579 / 1000000000) / 16) (1848959149 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1359 / 64000) : ℝ) (17 / 800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3277885099 / 1000000000) (3277988579 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1359 / 64000) (17 / 800) (1043383450131 / 1000000000000) (521708028187 / 500000000000) (3277885099 / 1000000000) (3277988579 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1359 / 64000) (17 / 800) (3277885099 / 1000000000) (3277988579 / 1000000000) (13399943 / 250000000000) (10723283 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3277885099 / 1000000000) (3277988579 / 1000000000) (924461637 / 500000000) (1848959149 / 1000000000) (13399943 / 250000000000) (10723283 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0111 :
    ∀ t ∈ Set.Icc ((17 / 800) : ℝ) (1361 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1043416056373 / 1000000000000) : ℝ) ≤ Real.exp (2 * (17 / 800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (17 / 800)) (1043416056373 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1361 / 64000) : ℝ)) ≤ (208689732727 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1361 / 64000)) (208689732727 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((924479393 / 500000000) : ℝ) ≤ Real.exp (3 * (655597507 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (655597507 / 200000000) / 16) (924479393 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1639045509 / 500000000) : ℝ) / 16) ≤ (1848994663 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1639045509 / 500000000) / 16) (1848994663 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((17 / 800) : ℝ) (1361 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (655597507 / 200000000) (1639045509 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (17 / 800) (1361 / 64000) (1043416056373 / 1000000000000) (208689732727 / 200000000000) (655597507 / 200000000) (1639045509 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (17 / 800) (1361 / 64000) (655597507 / 200000000) (1639045509 / 500000000) (26791651 / 500000000000) (53599941 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (655597507 / 200000000) (1639045509 / 500000000) (924479393 / 500000000) (1848994663 / 1000000000) (26791651 / 500000000000) (53599941 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0112 :
    ∀ t ∈ Set.Icc ((1361 / 64000) : ℝ) (681 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((521724331817 / 500000000000) : ℝ) ≤ Real.exp (2 * (1361 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1361 / 64000)) (521724331817 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((681 / 32000) : ℝ)) ≤ (260870317979 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (681 / 32000)) (260870317979 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((18489943 / 10000000) : ℝ) ≤ Real.exp (3 * (1639044987 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1639044987 / 500000000) / 16) (18489943 / 10000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((163909673 / 50000000) : ℝ) / 16) ≤ (1849030179 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (163909673 / 50000000) / 16) (1849030179 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1361 / 64000) : ℝ) (681 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1639044987 / 500000000) (163909673 / 50000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1361 / 64000) (681 / 32000) (521724331817 / 500000000000) (260870317979 / 250000000000) (1639044987 / 500000000) (163909673 / 50000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1361 / 64000) (681 / 32000) (1639044987 / 500000000) (163909673 / 50000000) (53566837 / 1000000000000) (53583471 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1639044987 / 500000000) (163909673 / 50000000) (18489943 / 10000000) (1849030179 / 1000000000) (53566837 / 1000000000000) (53583471 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0113 :
    ∀ t ∈ Set.Icc ((681 / 32000) : ℝ) (1363 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((208696254383 / 200000000000) : ℝ) ≤ Real.exp (2 * (681 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (681 / 32000)) (208696254383 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1363 / 64000) : ℝ)) ≤ (208702776243 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1363 / 64000)) (208702776243 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((231128727 / 125000000) : ℝ) ≤ Real.exp (3 * (655638483 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (655638483 / 200000000) / 16) (231128727 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((655659181 / 200000000) : ℝ) / 16) ≤ (57783303 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (655659181 / 200000000) / 16) (57783303 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((681 / 32000) : ℝ) (1363 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (655638483 / 200000000) (655659181 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (681 / 32000) (1363 / 64000) (208696254383 / 200000000000) (208702776243 / 200000000000) (655638483 / 200000000) (655659181 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (681 / 32000) (1363 / 64000) (655638483 / 200000000) (655659181 / 200000000) (53550377 / 1000000000000) (26783503 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (655638483 / 200000000) (655659181 / 200000000) (231128727 / 125000000) (57783303 / 31250000) (53550377 / 1000000000000) (26783503 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0114 :
    ∀ t ∈ Set.Icc ((1363 / 64000) : ℝ) (341 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((521756940607 / 500000000000) : ℝ) ≤ Real.exp (2 * (1363 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1363 / 64000)) (521756940607 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((341 / 16000) : ℝ)) ≤ (1043546491533 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (341 / 16000)) (1043546491533 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1849065333 / 1000000000) : ℝ) ≤ Real.exp (3 * (3278294861 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3278294861 / 1000000000) / 16) (1849065333 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3278398353 / 1000000000) : ℝ) / 16) ≤ (369820243 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3278398353 / 1000000000) / 16) (369820243 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1363 / 64000) : ℝ) (341 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3278294861 / 1000000000) (3278398353 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1363 / 64000) (341 / 16000) (521756940607 / 500000000000) (1043546491533 / 1000000000000) (3278294861 / 1000000000) (3278398353 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1363 / 64000) (341 / 16000) (3278294861 / 1000000000) (3278398353 / 1000000000) (53533921 / 1000000000000) (26775273 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3278294861 / 1000000000) (3278398353 / 1000000000) (1849065333 / 1000000000) (369820243 / 200000000) (53533921 / 1000000000000) (26775273 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0115 :
    ∀ t ∈ Set.Icc ((341 / 16000) : ℝ) (273 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((260886622883 / 250000000000) : ℝ) ≤ Real.exp (2 * (341 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (341 / 16000)) (260886622883 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((273 / 12800) : ℝ)) ≤ (1043579102871 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (273 / 12800)) (1043579102871 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((462275213 / 250000000) : ℝ) ≤ Real.exp (3 * (3278397309 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3278397309 / 1000000000) / 16) (462275213 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((655700161 / 200000000) : ℝ) / 16) ≤ (57785523 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (655700161 / 200000000) / 16) (57785523 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((341 / 16000) : ℝ) (273 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3278397309 / 1000000000) (655700161 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (341 / 16000) (273 / 12800) (260886622883 / 250000000000) (1043579102871 / 1000000000000) (3278397309 / 1000000000) (655700161 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (341 / 16000) (273 / 12800) (3278397309 / 1000000000) (655700161 / 200000000) (53517469 / 1000000000000) (5353409 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3278397309 / 1000000000) (655700161 / 200000000) (462275213 / 250000000) (57785523 / 31250000) (53517469 / 1000000000000) (5353409 / 100000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0116 :
    ∀ t ∈ Set.Icc ((273 / 12800) : ℝ) (683 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((104357910287 / 100000000000) : ℝ) ≤ Real.exp (2 * (273 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (273 / 12800)) (104357910287 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((683 / 32000) : ℝ)) ≤ (1043611715227 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (683 / 32000)) (1043611715227 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1849136373 / 1000000000) : ℝ) ≤ Real.exp (3 * (40981247 / 12500000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (40981247 / 12500000) / 16) (1849136373 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((163930163 / 50000000) : ℝ) / 16) ≤ (1849172259 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (163930163 / 50000000) / 16) (1849172259 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((273 / 12800) : ℝ) (683 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (40981247 / 12500000) (163930163 / 50000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (273 / 12800) (683 / 32000) (104357910287 / 100000000000) (1043611715227 / 1000000000000) (40981247 / 12500000) (163930163 / 50000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (273 / 12800) (683 / 32000) (40981247 / 12500000) (163930163 / 50000000) (53501023 / 1000000000000) (53517639 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (40981247 / 12500000) (163930163 / 50000000) (1849136373 / 1000000000) (1849172259 / 1000000000) (53501023 / 1000000000000) (53517639 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0117 :
    ∀ t ∈ Set.Icc ((683 / 32000) : ℝ) (1367 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((521805857613 / 500000000000) : ℝ) ≤ Real.exp (2 * (683 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (683 / 32000)) (521805857613 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1367 / 64000) : ℝ)) ≤ (1043644328603 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1367 / 64000)) (1043644328603 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((231146487 / 125000000) : ℝ) ≤ Real.exp (3 * (655720443 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (655720443 / 200000000) / 16) (231146487 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1639352859 / 500000000) : ℝ) / 16) ≤ (231150973 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1639352859 / 500000000) / 16) (231150973 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((683 / 32000) : ℝ) (1367 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (655720443 / 200000000) (1639352859 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (683 / 32000) (1367 / 64000) (521805857613 / 500000000000) (1043644328603 / 1000000000000) (655720443 / 200000000) (1639352859 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (683 / 32000) (1367 / 64000) (655720443 / 200000000) (1639352859 / 500000000) (2674229 / 50000000000) (6687649 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (655720443 / 200000000) (1639352859 / 500000000) (231146487 / 125000000) (231150973 / 125000000) (2674229 / 50000000000) (6687649 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0118 :
    ∀ t ∈ Set.Icc ((1367 / 64000) : ℝ) (171 / 8000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((521822164301 / 500000000000) : ℝ) ≤ Real.exp (2 * (1367 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1367 / 64000)) (521822164301 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((171 / 8000) : ℝ)) ≤ (521838471499 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (171 / 8000)) (521838471499 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((92460371 / 50000000) : ℝ) ≤ Real.exp (3 * (3278704673 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3278704673 / 1000000000) / 16) (92460371 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3278808179 / 1000000000) : ℝ) / 16) ≤ (184924331 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3278808179 / 1000000000) / 16) (184924331 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1367 / 64000) : ℝ) (171 / 8000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3278704673 / 1000000000) (3278808179 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1367 / 64000) (171 / 8000) (521822164301 / 500000000000) (521838471499 / 500000000000) (3278704673 / 1000000000) (3278808179 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1367 / 64000) (171 / 8000) (3278704673 / 1000000000) (3278808179 / 1000000000) (26734071 / 500000000000) (53484749 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3278704673 / 1000000000) (3278808179 / 1000000000) (92460371 / 50000000) (184924331 / 100000000) (26734071 / 500000000000) (53484749 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0119 :
    ∀ t ∈ Set.Icc ((171 / 8000) : ℝ) (1369 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1043676942997 / 1000000000000) : ℝ) ≤ Real.exp (2 * (171 / 8000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (171 / 8000)) (1043676942997 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1369 / 64000) : ℝ)) ≤ (260927389603 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1369 / 64000)) (260927389603 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1849242947 / 1000000000) : ℝ) ≤ Real.exp (3 * (1639403567 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1639403567 / 500000000) / 16) (1849242947 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3278910643 / 1000000000) : ℝ) / 16) ≤ (924639419 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3278910643 / 1000000000) / 16) (924639419 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((171 / 8000) : ℝ) (1369 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1639403567 / 500000000) (3278910643 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (171 / 8000) (1369 / 64000) (1043676942997 / 1000000000000) (260927389603 / 250000000000) (1639403567 / 500000000) (3278910643 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (171 / 8000) (1369 / 64000) (1639403567 / 500000000) (3278910643 / 1000000000) (53451709 / 1000000000000) (53468311 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1639403567 / 500000000) (3278910643 / 1000000000) (1849242947 / 1000000000) (924639419 / 500000000) (53451709 / 1000000000000) (53468311 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch005 :
    ∀ t ∈ Set.Icc ((1349 / 64000) : ℝ) (1369 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0100
      hpThetaDensityTwoTermCompact_cell0101)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0102
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0103
      hpThetaDensityTwoTermCompact_cell0104)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0105
      hpThetaDensityTwoTermCompact_cell0106)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0107
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0108
      hpThetaDensityTwoTermCompact_cell0109))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0110
      hpThetaDensityTwoTermCompact_cell0111)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0112
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0113
      hpThetaDensityTwoTermCompact_cell0114)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0115
      hpThetaDensityTwoTermCompact_cell0116)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0117
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0118
      hpThetaDensityTwoTermCompact_cell0119)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch005
end HodgeProofHP
