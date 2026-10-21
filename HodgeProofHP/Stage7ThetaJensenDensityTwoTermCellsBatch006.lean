/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0120 :
    ∀ t ∈ Set.Icc ((1369 / 64000) : ℝ) (137 / 6400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1043709558411 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1369 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1369 / 64000)) (1043709558411 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((137 / 6400) : ℝ)) ≤ (208748434969 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (137 / 6400)) (208748434969 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((73971139 / 40000000) : ℝ) ≤ Real.exp (3 * (3278909599 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3278909599 / 1000000000) / 16) (73971139 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3279013111 / 1000000000) : ℝ) / 16) ≤ (28895537 / 15625000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3279013111 / 1000000000) / 16) (28895537 / 15625000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1369 / 64000) : ℝ) (137 / 6400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3278909599 / 1000000000) (3279013111 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1369 / 64000) (137 / 6400) (1043709558411 / 1000000000000) (208748434969 / 200000000000) (3278909599 / 1000000000) (3279013111 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1369 / 64000) (137 / 6400) (3278909599 / 1000000000) (3279013111 / 1000000000) (53435281 / 1000000000000) (26725939 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3278909599 / 1000000000) (3279013111 / 1000000000) (73971139 / 40000000) (28895537 / 15625000) (53435281 / 1000000000000) (26725939 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0121 :
    ∀ t ∈ Set.Icc ((137 / 6400) : ℝ) (1371 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((260935543711 / 250000000000) : ℝ) ≤ Real.exp (2 * (137 / 6400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (137 / 6400)) (260935543711 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1371 / 64000) : ℝ)) ≤ (521887396149 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1371 / 64000)) (521887396149 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((369862801 / 200000000) : ℝ) ≤ Real.exp (3 * (1639506033 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1639506033 / 500000000) / 16) (369862801 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1639557791 / 500000000) : ℝ) / 16) ≤ (18493499 / 10000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1639557791 / 500000000) / 16) (18493499 / 10000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((137 / 6400) : ℝ) (1371 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1639506033 / 500000000) (1639557791 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (137 / 6400) (1371 / 64000) (260935543711 / 250000000000) (521887396149 / 500000000000) (1639506033 / 500000000) (1639557791 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (137 / 6400) (1371 / 64000) (1639506033 / 500000000) (1639557791 / 500000000) (6677357 / 125000000000) (53435449 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1639506033 / 500000000) (1639557791 / 500000000) (369862801 / 200000000) (18493499 / 10000000) (6677357 / 125000000000) (53435449 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0122 :
    ∀ t ∈ Set.Icc ((1371 / 64000) : ℝ) (343 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1043774792297 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1371 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1371 / 64000)) (1043774792297 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((343 / 16000) : ℝ)) ≤ (104380741077 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (343 / 16000)) (104380741077 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1849349537 / 1000000000) : ℝ) ≤ Real.exp (3 * (3279114537 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3279114537 / 1000000000) / 16) (1849349537 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((409902257 / 125000000) : ℝ) / 16) ≤ (1849385433 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (409902257 / 125000000) / 16) (1849385433 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1371 / 64000) : ℝ) (343 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3279114537 / 1000000000) (409902257 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1371 / 64000) (343 / 16000) (1043774792297 / 1000000000000) (104380741077 / 100000000000) (3279114537 / 1000000000) (409902257 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1371 / 64000) (343 / 16000) (3279114537 / 1000000000) (409902257 / 125000000) (53402437 / 1000000000000) (2136761 / 40000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3279114537 / 1000000000) (409902257 / 125000000) (1849349537 / 1000000000) (1849385433 / 1000000000) (53402437 / 1000000000000) (2136761 / 40000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0123 :
    ∀ t ∈ Set.Icc ((343 / 16000) : ℝ) (1373 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1043807410769 / 1000000000000) : ℝ) ≤ Real.exp (2 * (343 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (343 / 16000)) (1043807410769 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1373 / 64000) : ℝ)) ≤ (1043840030261 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1373 / 64000)) (1043840030261 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((184938507 / 100000000) : ℝ) ≤ Real.exp (3 * (3279217011 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3279217011 / 1000000000) / 16) (184938507 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3279320533 / 1000000000) : ℝ) / 16) ≤ (1849420969 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3279320533 / 1000000000) / 16) (1849420969 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((343 / 16000) : ℝ) (1373 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3279217011 / 1000000000) (3279320533 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (343 / 16000) (1373 / 64000) (1043807410769 / 1000000000000) (1043840030261 / 1000000000000) (3279217011 / 1000000000) (3279320533 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (343 / 16000) (1373 / 64000) (3279217011 / 1000000000) (3279320533 / 1000000000) (26693011 / 500000000000) (26701303 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3279217011 / 1000000000) (3279320533 / 1000000000) (184938507 / 100000000) (1849420969 / 1000000000) (26693011 / 500000000000) (26701303 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0124 :
    ∀ t ∈ Set.Icc ((1373 / 64000) : ℝ) (687 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((52192001513 / 50000000000) : ℝ) ≤ Real.exp (2 * (1373 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1373 / 64000)) (52192001513 / 50000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((687 / 32000) : ℝ)) ≤ (260968162693 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (687 / 32000)) (260968162693 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((369884121 / 200000000) : ℝ) ≤ Real.exp (3 * (51239367 / 15625000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (51239367 / 15625000) / 16) (369884121 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3279423013 / 1000000000) : ℝ) / 16) ≤ (924728253 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3279423013 / 1000000000) / 16) (924728253 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1373 / 64000) : ℝ) (687 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (51239367 / 15625000) (3279423013 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1373 / 64000) (687 / 32000) (52192001513 / 50000000000) (260968162693 / 250000000000) (51239367 / 15625000) (3279423013 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1373 / 64000) (687 / 32000) (51239367 / 15625000) (3279423013 / 1000000000) (53369611 / 1000000000000) (53386191 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (51239367 / 15625000) (3279423013 / 1000000000) (369884121 / 200000000) (924728253 / 500000000) (53369611 / 1000000000000) (53386191 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0125 :
    ∀ t ∈ Set.Icc ((687 / 32000) : ℝ) (11 / 512), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1043872650771 / 1000000000000) : ℝ) ≤ Real.exp (2 * (687 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (687 / 32000)) (1043872650771 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((11 / 512) : ℝ)) ≤ (521952636151 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (11 / 512)) (521952636151 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((924728071 / 500000000) : ℝ) ≤ Real.exp (3 * (204963873 / 62500000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (204963873 / 62500000) / 16) (924728071 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3279525497 / 1000000000) : ℝ) / 16) ≤ (369898409 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3279525497 / 1000000000) / 16) (369898409 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((687 / 32000) : ℝ) (11 / 512),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (204963873 / 62500000) (3279525497 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (687 / 32000) (11 / 512) (1043872650771 / 1000000000000) (521952636151 / 500000000000) (204963873 / 62500000) (3279525497 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (687 / 32000) (11 / 512) (204963873 / 62500000) (3279525497 / 1000000000) (10670641 / 200000000000) (2668489 / 50000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (204963873 / 62500000) (3279525497 / 1000000000) (924728071 / 500000000) (369898409 / 200000000) (10670641 / 200000000000) (2668489 / 50000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0126 :
    ∀ t ∈ Set.Icc ((11 / 512) : ℝ) (43 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1043905272301 / 1000000000000) : ℝ) ≤ Real.exp (2 * (11 / 512)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (11 / 512)) (1043905272301 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((43 / 2000) : ℝ)) ≤ (1043937894851 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43 / 2000)) (1043937894851 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1849491681 / 1000000000) : ℝ) ≤ Real.exp (3 * (819881113 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (819881113 / 250000000) / 16) (1849491681 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3279627983 / 1000000000) : ℝ) / 16) ≤ (369905517 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3279627983 / 1000000000) / 16) (369905517 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((11 / 512) : ℝ) (43 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (819881113 / 250000000) (3279627983 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (11 / 512) (43 / 2000) (1043905272301 / 1000000000000) (1043937894851 / 1000000000000) (819881113 / 250000000) (3279627983 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (11 / 512) (43 / 2000) (819881113 / 250000000) (3279627983 / 1000000000) (13334201 / 250000000000) (26676687 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (819881113 / 250000000) (3279627983 / 1000000000) (1849491681 / 1000000000) (369905517 / 200000000) (13334201 / 250000000000) (26676687 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0127 :
    ∀ t ∈ Set.Icc ((43 / 2000) : ℝ) (1377 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((20878757897 / 20000000000) : ℝ) ≤ Real.exp (2 * (43 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43 / 2000)) (20878757897 / 20000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1377 / 64000) : ℝ)) ≤ (52198525921 / 50000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1377 / 64000)) (52198525921 / 50000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((924763611 / 500000000) : ℝ) ≤ Real.exp (3 * (1639813469 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1639813469 / 500000000) / 16) (924763611 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3279730473 / 1000000000) : ℝ) / 16) ≤ (231195391 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3279730473 / 1000000000) / 16) (231195391 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((43 / 2000) : ℝ) (1377 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1639813469 / 500000000) (3279730473 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (43 / 2000) (1377 / 64000) (20878757897 / 20000000000) (52198525921 / 50000000000) (1639813469 / 500000000) (3279730473 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (43 / 2000) (1377 / 64000) (1639813469 / 500000000) (3279730473 / 1000000000) (53320407 / 1000000000000) (13334243 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1639813469 / 500000000) (3279730473 / 1000000000) (924763611 / 500000000) (231195391 / 125000000) (53320407 / 1000000000000) (13334243 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0128 :
    ∀ t ∈ Set.Icc ((1377 / 64000) : ℝ) (689 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1043970518419 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1377 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1377 / 64000)) (1043970518419 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((689 / 32000) : ℝ)) ≤ (1044003143009 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (689 / 32000)) (1044003143009 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((462390691 / 250000000) : ℝ) ≤ Real.exp (3 * (819932357 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (819932357 / 250000000) / 16) (462390691 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3279832967 / 1000000000) : ℝ) / 16) ≤ (115599917 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3279832967 / 1000000000) / 16) (115599917 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1377 / 64000) : ℝ) (689 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (819932357 / 250000000) (3279832967 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1377 / 64000) (689 / 32000) (1043970518419 / 1000000000000) (1044003143009 / 1000000000000) (819932357 / 250000000) (3279832967 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1377 / 64000) (689 / 32000) (819932357 / 250000000) (3279832967 / 1000000000) (26652007 / 500000000000) (416567 / 7812500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (819932357 / 250000000) (3279832967 / 1000000000) (462390691 / 250000000) (115599917 / 62500000) (26652007 / 500000000000) (416567 / 7812500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0129 :
    ∀ t ∈ Set.Icc ((689 / 32000) : ℝ) (1379 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((32625098219 / 31250000000) : ℝ) ≤ Real.exp (2 * (689 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (689 / 32000)) (32625098219 / 31250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1379 / 64000) : ℝ)) ≤ (1044035768617 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1379 / 64000)) (1044035768617 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1849598309 / 1000000000) : ℝ) ≤ Real.exp (3 * (1639915961 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1639915961 / 500000000) / 16) (1849598309 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3279935463 / 1000000000) : ℝ) / 16) ≤ (924817109 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3279935463 / 1000000000) / 16) (924817109 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((689 / 32000) : ℝ) (1379 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1639915961 / 500000000) (3279935463 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (689 / 32000) (1379 / 64000) (32625098219 / 31250000000) (1044035768617 / 1000000000000) (1639915961 / 500000000) (3279935463 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (689 / 32000) (1379 / 64000) (1639915961 / 500000000) (3279935463 / 1000000000) (26643813 / 500000000000) (53304183 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1639915961 / 500000000) (3279935463 / 1000000000) (1849598309 / 1000000000) (924817109 / 500000000) (26643813 / 500000000000) (53304183 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0130 :
    ∀ t ∈ Set.Icc ((1379 / 64000) : ℝ) (69 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((130504471077 / 125000000000) : ℝ) ≤ Real.exp (2 * (1379 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1379 / 64000)) (130504471077 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((69 / 3200) : ℝ)) ≤ (261017098811 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (69 / 3200)) (261017098811 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((369926771 / 200000000) : ℝ) ≤ Real.exp (3 * (1639967209 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1639967209 / 500000000) / 16) (369926771 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3280037963 / 1000000000) : ℝ) / 16) ≤ (924834883 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3280037963 / 1000000000) / 16) (924834883 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1379 / 64000) : ℝ) (69 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1639967209 / 500000000) (3280037963 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1379 / 64000) (69 / 3200) (130504471077 / 125000000000) (261017098811 / 250000000000) (1639967209 / 500000000) (3280037963 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1379 / 64000) (69 / 3200) (1639967209 / 500000000) (3280037963 / 1000000000) (53271243 / 1000000000000) (10657559 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1639967209 / 500000000) (3280037963 / 1000000000) (369926771 / 200000000) (924834883 / 500000000) (53271243 / 1000000000000) (10657559 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0131 :
    ∀ t ∈ Set.Icc ((69 / 3200) : ℝ) (1381 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1044068395243 / 1000000000000) : ℝ) ≤ Real.exp (2 * (69 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (69 / 3200)) (1044068395243 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1381 / 64000) : ℝ)) ≤ (1044101022891 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1381 / 64000)) (1044101022891 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((924834701 / 500000000) : ℝ) ≤ Real.exp (3 * (3280036917 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3280036917 / 1000000000) / 16) (924834701 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((656028093 / 200000000) : ℝ) / 16) ≤ (369941063 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (656028093 / 200000000) / 16) (369941063 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((69 / 3200) : ℝ) (1381 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3280036917 / 1000000000) (656028093 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (69 / 3200) (1381 / 64000) (1044068395243 / 1000000000000) (1044101022891 / 1000000000000) (3280036917 / 1000000000) (656028093 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (69 / 3200) (1381 / 64000) (3280036917 / 1000000000) (656028093 / 200000000) (10650973 / 200000000000) (13317853 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3280036917 / 1000000000) (656028093 / 200000000) (924834701 / 500000000) (369941063 / 200000000) (10650973 / 200000000000) (13317853 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0132 :
    ∀ t ∈ Set.Icc ((1381 / 64000) : ℝ) (691 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((104410102289 / 100000000000) : ℝ) ≤ Real.exp (2 * (1381 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1381 / 64000)) (104410102289 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((691 / 32000) : ℝ)) ≤ (522066825779 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (691 / 32000)) (522066825779 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((231213119 / 125000000) : ℝ) ≤ Real.exp (3 * (164006971 / 50000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (164006971 / 50000000) / 16) (231213119 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3280242971 / 1000000000) : ℝ) / 16) ≤ (1849740867 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3280242971 / 1000000000) / 16) (1849740867 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1381 / 64000) : ℝ) (691 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (164006971 / 50000000) (3280242971 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1381 / 64000) (691 / 32000) (104410102289 / 100000000000) (522066825779 / 500000000000) (164006971 / 50000000) (3280242971 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1381 / 64000) (691 / 32000) (164006971 / 50000000) (3280242971 / 1000000000) (5323849 / 100000000000) (53255033 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (164006971 / 50000000) (3280242971 / 1000000000) (231213119 / 125000000) (1849740867 / 1000000000) (5323849 / 100000000000) (53255033 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0133 :
    ∀ t ∈ Set.Icc ((691 / 32000) : ℝ) (1383 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1044133651557 / 1000000000000) : ℝ) ≤ Real.exp (2 * (691 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (691 / 32000)) (1044133651557 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1383 / 64000) : ℝ)) ≤ (261041570311 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1383 / 64000)) (261041570311 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1849740503 / 1000000000) : ℝ) ≤ Real.exp (3 * (1640120963 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1640120963 / 500000000) / 16) (1849740503 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((82008637 / 25000000) : ℝ) / 16) ≤ (92488821 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (82008637 / 25000000) / 16) (92488821 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((691 / 32000) : ℝ) (1383 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1640120963 / 500000000) (82008637 / 25000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (691 / 32000) (1383 / 64000) (1044133651557 / 1000000000000) (261041570311 / 250000000000) (1640120963 / 500000000) (82008637 / 25000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (691 / 32000) (1383 / 64000) (1640120963 / 500000000) (82008637 / 25000000) (1330553 / 25000000000) (53238659 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1640120963 / 500000000) (82008637 / 25000000) (1849740503 / 1000000000) (92488821 / 50000000) (1330553 / 25000000000) (53238659 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0134 :
    ∀ t ∈ Set.Icc ((1383 / 64000) : ℝ) (173 / 8000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1044166281243 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1383 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1383 / 64000)) (1044166281243 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((173 / 8000) : ℝ)) ≤ (1044198911951 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (173 / 8000)) (1044198911951 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1849776057 / 1000000000) : ℝ) ≤ Real.exp (3 * (656068887 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (656068887 / 200000000) / 16) (1849776057 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3280447993 / 1000000000) : ℝ) / 16) ≤ (73992479 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3280447993 / 1000000000) / 16) (73992479 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1383 / 64000) : ℝ) (173 / 8000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (656068887 / 200000000) (3280447993 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1383 / 64000) (173 / 8000) (1044166281243 / 1000000000000) (1044198911951 / 1000000000000) (656068887 / 200000000) (3280447993 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1383 / 64000) (173 / 8000) (656068887 / 200000000) (3280447993 / 1000000000) (10641151 / 200000000000) (3326393 / 62500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (656068887 / 200000000) (3280447993 / 1000000000) (1849776057 / 1000000000) (73992479 / 40000000) (10641151 / 200000000000) (3326393 / 62500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0135 :
    ∀ t ∈ Set.Icc ((173 / 8000) : ℝ) (277 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((20883978239 / 20000000000) : ℝ) ≤ Real.exp (2 * (173 / 8000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (173 / 8000)) (20883978239 / 20000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((277 / 12800) : ℝ)) ≤ (261057885919 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (277 / 12800)) (261057885919 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((462452903 / 250000000) : ℝ) ≤ Real.exp (3 * (820111737 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (820111737 / 250000000) / 16) (462452903 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((820137627 / 250000000) : ℝ) / 16) ≤ (462461883 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (820137627 / 250000000) / 16) (462461883 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((173 / 8000) : ℝ) (277 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (820111737 / 250000000) (820137627 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (173 / 8000) (277 / 12800) (20883978239 / 20000000000) (261057885919 / 250000000000) (820111737 / 250000000) (820137627 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (173 / 8000) (277 / 12800) (820111737 / 250000000) (820137627 / 250000000) (26594697 / 500000000000) (53205923 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (820111737 / 250000000) (820137627 / 250000000) (462452903 / 250000000) (462461883 / 250000000) (26594697 / 500000000000) (53205923 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0136 :
    ∀ t ∈ Set.Icc ((277 / 12800) : ℝ) (693 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((41769261747 / 40000000000) : ℝ) ≤ Real.exp (2 * (277 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (277 / 12800)) (41769261747 / 40000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((693 / 32000) : ℝ)) ≤ (522132088211 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (693 / 32000)) (522132088211 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((14451931 / 7812500) : ℝ) ≤ Real.exp (3 * (3280549463 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3280549463 / 1000000000) / 16) (14451931 / 7812500) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3280653027 / 1000000000) : ℝ) / 16) ≤ (1849883091 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3280653027 / 1000000000) / 16) (1849883091 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((277 / 12800) : ℝ) (693 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3280549463 / 1000000000) (3280653027 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (277 / 12800) (693 / 32000) (41769261747 / 40000000000) (522132088211 / 500000000000) (3280549463 / 1000000000) (3280653027 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (277 / 12800) (693 / 32000) (3280549463 / 1000000000) (3280653027 / 1000000000) (26586519 / 500000000000) (53189563 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3280549463 / 1000000000) (3280653027 / 1000000000) (14451931 / 7812500) (1849883091 / 1000000000) (26586519 / 500000000000) (53189563 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0137 :
    ∀ t ∈ Set.Icc ((693 / 32000) : ℝ) (1387 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1044264176421 / 1000000000000) : ℝ) ≤ Real.exp (2 * (693 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (693 / 32000)) (1044264176421 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1387 / 64000) : ℝ)) ≤ (261074202547 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1387 / 64000)) (261074202547 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1849882727 / 1000000000) : ℝ) ≤ Real.exp (3 * (1640325991 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1640325991 / 500000000) / 16) (1849882727 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3280755549 / 1000000000) : ℝ) / 16) ≤ (1849918651 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3280755549 / 1000000000) / 16) (1849918651 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((693 / 32000) : ℝ) (1387 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1640325991 / 500000000) (3280755549 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (693 / 32000) (1387 / 64000) (1044264176421 / 1000000000000) (261074202547 / 250000000000) (1640325991 / 500000000) (3280755549 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (693 / 32000) (1387 / 64000) (1640325991 / 500000000) (3280755549 / 1000000000) (26578343 / 500000000000) (26586603 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1640325991 / 500000000) (3280755549 / 1000000000) (1849882727 / 1000000000) (1849918651 / 1000000000) (26578343 / 500000000000) (26586603 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0138 :
    ∀ t ∈ Set.Icc ((1387 / 64000) : ℝ) (347 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1044296810187 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1387 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1387 / 64000)) (1044296810187 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((347 / 16000) : ℝ)) ≤ (1044329444973 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (347 / 16000)) (1044329444973 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((115619893 / 62500000) : ℝ) ≤ Real.exp (3 * (410094313 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (410094313 / 125000000) / 16) (115619893 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((131234323 / 40000000) : ℝ) / 16) ≤ (924977107 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (131234323 / 40000000) / 16) (924977107 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1387 / 64000) : ℝ) (347 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (410094313 / 125000000) (131234323 / 40000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1387 / 64000) (347 / 16000) (1044296810187 / 1000000000000) (1044329444973 / 1000000000000) (410094313 / 125000000) (131234323 / 40000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1387 / 64000) (347 / 16000) (410094313 / 125000000) (131234323 / 40000000) (53140339 / 1000000000000) (26578427 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (410094313 / 125000000) (131234323 / 40000000) (115619893 / 62500000) (924977107 / 500000000) (53140339 / 1000000000000) (26578427 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0139 :
    ∀ t ∈ Set.Icc ((347 / 16000) : ℝ) (1389 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((261082361243 / 250000000000) : ℝ) ≤ Real.exp (2 * (347 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (347 / 16000)) (261082361243 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1389 / 64000) : ℝ)) ≤ (522181040389 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1389 / 64000)) (522181040389 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((36999077 / 20000000) : ℝ) ≤ Real.exp (3 * (3280857029 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3280857029 / 1000000000) / 16) (36999077 / 20000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3280960603 / 1000000000) : ℝ) / 16) ≤ (1849989777 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3280960603 / 1000000000) / 16) (1849989777 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((347 / 16000) : ℝ) (1389 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3280857029 / 1000000000) (3280960603 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (347 / 16000) (1389 / 64000) (261082361243 / 250000000000) (522181040389 / 500000000000) (3280857029 / 1000000000) (3280960603 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (347 / 16000) (1389 / 64000) (3280857029 / 1000000000) (3280960603 / 1000000000) (53123997 / 1000000000000) (53140507 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3280857029 / 1000000000) (3280960603 / 1000000000) (36999077 / 20000000) (1849989777 / 1000000000) (53123997 / 1000000000000) (53140507 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch006 :
    ∀ t ∈ Set.Icc ((1369 / 64000) : ℝ) (1389 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0120
      hpThetaDensityTwoTermCompact_cell0121)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0122
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0123
      hpThetaDensityTwoTermCompact_cell0124)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0125
      hpThetaDensityTwoTermCompact_cell0126)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0127
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0128
      hpThetaDensityTwoTermCompact_cell0129))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0130
      hpThetaDensityTwoTermCompact_cell0131)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0132
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0133
      hpThetaDensityTwoTermCompact_cell0134)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0135
      hpThetaDensityTwoTermCompact_cell0136)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0137
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0138
      hpThetaDensityTwoTermCompact_cell0139)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch006
end HodgeProofHP
