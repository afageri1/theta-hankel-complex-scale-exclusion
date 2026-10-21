/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0060 :
    ∀ t ∈ Set.Icc ((131 / 6400) : ℝ) (2621 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1041786991823 / 1000000000000) : ℝ) ≤ Real.exp (2 * (131 / 6400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (131 / 6400)) (1041786991823 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2621 / 128000) : ℝ)) ≤ (1041803269873 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2621 / 128000)) (1041803269873 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((92359269 / 50000000) : ℝ) ≤ Real.exp (3 * (3272869679 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3272869679 / 1000000000) / 16) (92359269 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3272921861 / 1000000000) : ℝ) / 16) ≤ (369440691 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3272921861 / 1000000000) / 16) (369440691 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((131 / 6400) : ℝ) (2621 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3272869679 / 1000000000) (3272921861 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (131 / 6400) (2621 / 128000) (1041786991823 / 1000000000000) (1041803269873 / 1000000000000) (3272869679 / 1000000000) (3272921861 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (131 / 6400) (2621 / 128000) (3272869679 / 1000000000) (3272921861 / 1000000000) (680259 / 12500000000) (27214621 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3272869679 / 1000000000) (3272921861 / 1000000000) (92359269 / 50000000) (369440691 / 200000000) (680259 / 12500000000) (27214621 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0061 :
    ∀ t ∈ Set.Icc ((2621 / 128000) : ℝ) (1311 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((65112704367 / 62500000000) : ℝ) ≤ Real.exp (2 * (2621 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2621 / 128000)) (65112704367 / 62500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1311 / 64000) : ℝ)) ≤ (65113721761 / 62500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1311 / 64000)) (65113721761 / 62500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((461800773 / 250000000) : ℝ) ≤ Real.exp (3 * (1636460409 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1636460409 / 500000000) / 16) (461800773 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3272973 / 1000000) : ℝ) / 16) ≤ (1847221167 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3272973 / 1000000) / 16) (1847221167 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2621 / 128000) : ℝ) (1311 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1636460409 / 500000000) (3272973 / 1000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2621 / 128000) (1311 / 64000) (65112704367 / 62500000000) (65113721761 / 62500000000) (1636460409 / 500000000) (3272973 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2621 / 128000) (1311 / 64000) (1636460409 / 500000000) (3272973 / 1000000) (54412371 / 1000000000000) (13605223 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1636460409 / 500000000) (3272973 / 1000000) (461800773 / 250000000) (1847221167 / 1000000000) (54412371 / 1000000000000) (13605223 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0062 :
    ∀ t ∈ Set.Icc ((1311 / 64000) : ℝ) (41 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((41672781927 / 40000000000) : ℝ) ≤ Real.exp (2 * (1311 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1311 / 64000)) (41672781927 / 40000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41 / 2000) : ℝ)) ≤ (520926052773 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41 / 2000)) (520926052773 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((461805201 / 250000000) : ℝ) ≤ Real.exp (3 * (3272971957 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3272971957 / 1000000000) / 16) (461805201 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1636537641 / 500000000) : ℝ) / 16) ≤ (1847256593 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1636537641 / 500000000) / 16) (1847256593 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1311 / 64000) : ℝ) (41 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3272971957 / 1000000000) (1636537641 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1311 / 64000) (41 / 2000) (41672781927 / 40000000000) (520926052773 / 500000000000) (3272971957 / 1000000000) (1636537641 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1311 / 64000) (41 / 2000) (3272971957 / 1000000000) (1636537641 / 500000000) (27197839 / 500000000000) (54412543 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3272971957 / 1000000000) (1636537641 / 500000000) (461805201 / 250000000) (1847256593 / 1000000000) (27197839 / 500000000000) (54412543 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0063 :
    ∀ t ∈ Set.Icc ((41 / 2000) : ℝ) (1313 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((208370421109 / 200000000000) : ℝ) ≤ Real.exp (2 * (41 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41 / 2000)) (208370421109 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1313 / 64000) : ℝ)) ≤ (1041884663933 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1313 / 64000)) (1041884663933 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1847256231 / 1000000000) : ℝ) ≤ Real.exp (3 * (3273074239 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3273074239 / 1000000000) / 16) (1847256231 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((102286799 / 31250000) : ℝ) / 16) ≤ (1847292021 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (102286799 / 31250000) / 16) (1847292021 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41 / 2000) : ℝ) (1313 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3273074239 / 1000000000) (102286799 / 31250000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (41 / 2000) (1313 / 64000) (208370421109 / 200000000000) (1041884663933 / 1000000000000) (3273074239 / 1000000000) (102286799 / 31250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (41 / 2000) (1313 / 64000) (3273074239 / 1000000000) (102286799 / 31250000) (54378989 / 1000000000000) (54395849 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3273074239 / 1000000000) (102286799 / 31250000) (1847256231 / 1000000000) (1847292021 / 1000000000) (54378989 / 1000000000000) (54395849 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0064 :
    ∀ t ∈ Set.Icc ((1313 / 64000) : ℝ) (657 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((260471165983 / 250000000000) : ℝ) ≤ Real.exp (2 * (1313 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1313 / 64000)) (260471165983 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((657 / 32000) : ℝ)) ≤ (1041917223337 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (657 / 32000)) (1041917223337 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1847291659 / 1000000000) : ℝ) ≤ Real.exp (3 * (130927061 / 40000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (130927061 / 40000000) / 16) (1847291659 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((204579991 / 62500000) : ℝ) / 16) ≤ (1847327451 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (204579991 / 62500000) / 16) (1847327451 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1313 / 64000) : ℝ) (657 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (130927061 / 40000000) (204579991 / 62500000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1313 / 64000) (657 / 32000) (260471165983 / 250000000000) (1041917223337 / 1000000000000) (130927061 / 40000000) (204579991 / 62500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1313 / 64000) (657 / 32000) (130927061 / 40000000) (204579991 / 62500000) (849411 / 15625000000) (1359479 / 25000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (130927061 / 40000000) (204579991 / 62500000) (1847291659 / 1000000000) (1847327451 / 1000000000) (849411 / 15625000000) (1359479 / 25000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0065 :
    ∀ t ∈ Set.Icc ((657 / 32000) : ℝ) (263 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((130239652917 / 125000000000) : ℝ) ≤ Real.exp (2 * (657 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (657 / 32000)) (130239652917 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((263 / 12800) : ℝ)) ≤ (1041949783759 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (263 / 12800)) (1041949783759 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((115457943 / 62500000) : ℝ) ≤ Real.exp (3 * (3273278813 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3273278813 / 1000000000) / 16) (115457943 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((818345537 / 250000000) : ℝ) / 16) ≤ (923681441 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (818345537 / 250000000) / 16) (923681441 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((657 / 32000) : ℝ) (263 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3273278813 / 1000000000) (818345537 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (657 / 32000) (263 / 12800) (130239652917 / 125000000000) (1041949783759 / 1000000000000) (3273278813 / 1000000000) (818345537 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (657 / 32000) (263 / 12800) (3273278813 / 1000000000) (818345537 / 250000000) (6793203 / 125000000000) (13590619 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3273278813 / 1000000000) (818345537 / 250000000) (115457943 / 62500000) (923681441 / 500000000) (6793203 / 125000000000) (13590619 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0066 :
    ∀ t ∈ Set.Icc ((263 / 12800) : ℝ) (329 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((520974891879 / 500000000000) : ℝ) ≤ Real.exp (2 * (263 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (263 / 12800)) (520974891879 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((329 / 16000) : ℝ)) ≤ (1041982345199 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (329 / 16000)) (1041982345199 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((46184063 / 25000000) : ℝ) ≤ Real.exp (3 * (654676221 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (654676221 / 200000000) / 16) (46184063 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1636742221 / 500000000) : ℝ) / 16) ≤ (369479663 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1636742221 / 500000000) / 16) (369479663 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((263 / 12800) : ℝ) (329 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (654676221 / 200000000) (1636742221 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (263 / 12800) (329 / 16000) (520974891879 / 500000000000) (1041982345199 / 1000000000000) (654676221 / 200000000) (1636742221 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (263 / 12800) (329 / 16000) (654676221 / 200000000) (1636742221 / 500000000) (54328949 / 1000000000000) (13586449 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (654676221 / 200000000) (1636742221 / 500000000) (46184063 / 25000000) (369479663 / 200000000) (54328949 / 1000000000000) (13586449 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0067 :
    ∀ t ∈ Set.Icc ((329 / 16000) : ℝ) (1317 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((520991172599 / 500000000000) : ℝ) ≤ Real.exp (2 * (329 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (329 / 16000)) (520991172599 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1317 / 64000) : ℝ)) ≤ (130251863457 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1317 / 64000)) (130251863457 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1847397953 / 1000000000) : ℝ) ≤ Real.exp (3 * (3273483399 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3273483399 / 1000000000) / 16) (1847397953 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((163679337 / 50000000) : ℝ) / 16) ≤ (1477947 / 800000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (163679337 / 50000000) / 16) (1477947 / 800000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((329 / 16000) : ℝ) (1317 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3273483399 / 1000000000) (163679337 / 50000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (329 / 16000) (1317 / 64000) (520991172599 / 500000000000) (130251863457 / 125000000000) (3273483399 / 1000000000) (163679337 / 50000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (329 / 16000) (1317 / 64000) (3273483399 / 1000000000) (163679337 / 50000000) (54312279 / 1000000000000) (54329121 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3273483399 / 1000000000) (163679337 / 50000000) (1847397953 / 1000000000) (1477947 / 800000) (54312279 / 1000000000000) (54329121 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0068 :
    ∀ t ∈ Set.Icc ((1317 / 64000) : ℝ) (659 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((208402981531 / 200000000000) : ℝ) ≤ Real.exp (2 * (1317 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1317 / 64000)) (208402981531 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((659 / 32000) : ℝ)) ≤ (1042047471131 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (659 / 32000)) (1042047471131 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((461858347 / 250000000) : ℝ) ≤ Real.exp (3 * (3273585697 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3273585697 / 1000000000) / 16) (461858347 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3273689041 / 1000000000) : ℝ) / 16) ≤ (1847469187 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3273689041 / 1000000000) / 16) (1847469187 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1317 / 64000) : ℝ) (659 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3273585697 / 1000000000) (3273689041 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1317 / 64000) (659 / 32000) (208402981531 / 200000000000) (1042047471131 / 1000000000000) (3273585697 / 1000000000) (3273689041 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1317 / 64000) (659 / 32000) (3273585697 / 1000000000) (3273689041 / 1000000000) (13573903 / 250000000000) (1086249 / 20000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3273585697 / 1000000000) (3273689041 / 1000000000) (461858347 / 250000000) (1847469187 / 1000000000) (13573903 / 250000000000) (1086249 / 20000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0069 :
    ∀ t ∈ Set.Icc ((659 / 32000) : ℝ) (1319 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((104204747113 / 100000000000) : ℝ) ≤ Real.exp (2 * (659 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (659 / 32000)) (104204747113 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1319 / 64000) : ℝ)) ≤ (1042080035623 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1319 / 64000)) (1042080035623 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((73898753 / 40000000) : ℝ) ≤ Real.exp (3 * (1636843999 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1636843999 / 500000000) / 16) (73898753 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1636895673 / 500000000) : ℝ) / 16) ≤ (923752313 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1636895673 / 500000000) / 16) (923752313 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((659 / 32000) : ℝ) (1319 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1636843999 / 500000000) (1636895673 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (659 / 32000) (1319 / 64000) (104204747113 / 100000000000) (1042080035623 / 1000000000000) (1636843999 / 500000000) (1636895673 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (659 / 32000) (1319 / 64000) (1636843999 / 500000000) (1636895673 / 500000000) (54278951 / 1000000000000) (6786973 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1636843999 / 500000000) (1636895673 / 500000000) (73898753 / 40000000) (923752313 / 500000000) (54278951 / 1000000000000) (6786973 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0070 :
    ∀ t ∈ Set.Icc ((1319 / 64000) : ℝ) (33 / 1600), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((521040017811 / 500000000000) : ℝ) ≤ Real.exp (2 * (1319 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1319 / 64000)) (521040017811 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((33 / 1600) : ℝ)) ≤ (1042112601133 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (33 / 1600)) (1042112601133 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1847504263 / 1000000000) : ℝ) ≤ Real.exp (3 * (3273790303 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3273790303 / 1000000000) / 16) (1847504263 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3273893653 / 1000000000) : ℝ) / 16) ≤ (923770033 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3273893653 / 1000000000) / 16) (923770033 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1319 / 64000) : ℝ) (33 / 1600),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3273790303 / 1000000000) (3273893653 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1319 / 64000) (33 / 1600) (521040017811 / 500000000000) (1042112601133 / 1000000000000) (3273790303 / 1000000000) (3273893653 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1319 / 64000) (33 / 1600) (3273790303 / 1000000000) (3273893653 / 1000000000) (27131147 / 500000000000) (27139561 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3273790303 / 1000000000) (3273893653 / 1000000000) (1847504263 / 1000000000) (923770033 / 500000000) (27131147 / 500000000000) (27139561 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0071 :
    ∀ t ∈ Set.Icc ((33 / 1600) : ℝ) (1321 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((260528150283 / 250000000000) : ℝ) ≤ Real.exp (2 * (33 / 1600)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (33 / 1600)) (260528150283 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1321 / 64000) : ℝ)) ≤ (1042145167661 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1321 / 64000)) (1042145167661 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((230942463 / 125000000) : ℝ) ≤ Real.exp (3 * (327389261 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (327389261 / 100000000) / 16) (230942463 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((818498991 / 250000000) : ℝ) / 16) ≤ (461893877 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (818498991 / 250000000) / 16) (461893877 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((33 / 1600) : ℝ) (1321 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (327389261 / 100000000) (818498991 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (33 / 1600) (1321 / 64000) (260528150283 / 250000000000) (1042145167661 / 1000000000000) (327389261 / 100000000) (818498991 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (33 / 1600) (1321 / 64000) (327389261 / 100000000) (818498991 / 250000000) (27122821 / 500000000000) (10852493 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (327389261 / 100000000) (818498991 / 250000000) (230942463 / 125000000) (461893877 / 250000000) (27122821 / 500000000000) (10852493 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0072 :
    ∀ t ∈ Set.Icc ((1321 / 64000) : ℝ) (661 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((52107258383 / 50000000000) : ℝ) ≤ Real.exp (2 * (1321 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1321 / 64000)) (52107258383 / 50000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((661 / 32000) : ℝ)) ≤ (521088867603 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (661 / 32000)) (521088867603 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((923787573 / 500000000) : ℝ) ≤ Real.exp (3 * (3273994921 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3273994921 / 1000000000) / 16) (923787573 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1637049139 / 500000000) : ℝ) / 16) ≤ (230951369 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1637049139 / 500000000) / 16) (230951369 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1321 / 64000) : ℝ) (661 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3273994921 / 1000000000) (1637049139 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1321 / 64000) (661 / 32000) (52107258383 / 50000000000) (521088867603 / 500000000000) (3273994921 / 1000000000) (1637049139 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1321 / 64000) (661 / 32000) (3273994921 / 1000000000) (1637049139 / 500000000) (27114497 / 500000000000) (54245813 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3273994921 / 1000000000) (1637049139 / 500000000) (923787573 / 500000000) (230951369 / 125000000) (27114497 / 500000000000) (54245813 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0073 :
    ∀ t ∈ Set.Icc ((661 / 32000) : ℝ) (1323 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((208435547041 / 200000000000) : ℝ) ≤ Real.exp (2 * (661 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (661 / 32000)) (208435547041 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1323 / 64000) : ℝ)) ≤ (1042210303769 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1323 / 64000)) (1042210303769 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((184761059 / 100000000) : ℝ) ≤ Real.exp (3 * (654819447 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (654819447 / 200000000) / 16) (184761059 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((654840119 / 200000000) : ℝ) / 16) ≤ (923823199 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (654840119 / 200000000) / 16) (923823199 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((661 / 32000) : ℝ) (1323 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (654819447 / 200000000) (654840119 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (661 / 32000) (1323 / 64000) (208435547041 / 200000000000) (1042210303769 / 1000000000000) (654819447 / 200000000) (654840119 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (661 / 32000) (1323 / 64000) (654819447 / 200000000) (654840119 / 200000000) (54212351 / 1000000000000) (10845833 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (654819447 / 200000000) (654840119 / 200000000) (184761059 / 100000000) (923823199 / 500000000) (54212351 / 1000000000000) (10845833 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0074 :
    ∀ t ∈ Set.Icc ((1323 / 64000) : ℝ) (331 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((130276287971 / 125000000000) : ℝ) ≤ Real.exp (2 * (1323 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1323 / 64000)) (130276287971 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((331 / 16000) : ℝ)) ≤ (20844857467 / 20000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (331 / 16000)) (20844857467 / 20000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((461911509 / 250000000) : ℝ) ≤ Real.exp (3 * (6394921 / 1953125) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6394921 / 1953125) / 16) (461911509 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((818575729 / 250000000) : ℝ) / 16) ≤ (923840923 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (818575729 / 250000000) / 16) (923840923 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1323 / 64000) : ℝ) (331 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6394921 / 1953125) (818575729 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1323 / 64000) (331 / 16000) (130276287971 / 125000000000) (20844857467 / 20000000000) (6394921 / 1953125) (818575729 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1323 / 64000) (331 / 16000) (6394921 / 1953125) (818575729 / 250000000) (105851 / 1953125000) (27106261 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (6394921 / 1953125) (818575729 / 250000000) (461911509 / 250000000) (923840923 / 500000000) (105851 / 1953125000) (27106261 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0075 :
    ∀ t ∈ Set.Icc ((331 / 16000) : ℝ) (53 / 2560), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1042242873349 / 1000000000000) : ℝ) ≤ Real.exp (2 * (331 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (331 / 16000)) (1042242873349 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((53 / 2560) : ℝ)) ≤ (1042275443949 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (53 / 2560)) (1042275443949 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1847681483 / 1000000000) : ℝ) ≤ Real.exp (3 * (204643867 / 62500000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (204643867 / 62500000) / 16) (1847681483 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3274405239 / 1000000000) : ℝ) / 16) ≤ (369543459 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3274405239 / 1000000000) / 16) (369543459 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((331 / 16000) : ℝ) (53 / 2560),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (204643867 / 62500000) (3274405239 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (331 / 16000) (53 / 2560) (1042242873349 / 1000000000000) (1042275443949 / 1000000000000) (204643867 / 62500000) (3274405239 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (331 / 16000) (53 / 2560) (204643867 / 62500000) (3274405239 / 1000000000) (27089539 / 500000000000) (13548971 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (204643867 / 62500000) (3274405239 / 1000000000) (1847681483 / 1000000000) (369543459 / 200000000) (27089539 / 500000000000) (13548971 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0076 :
    ∀ t ∈ Set.Icc ((53 / 2560) : ℝ) (663 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((260568860987 / 250000000000) : ℝ) ≤ Real.exp (2 * (53 / 2560)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (53 / 2560)) (260568860987 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((663 / 32000) : ℝ)) ≤ (208461603113 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (663 / 32000)) (208461603113 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1847716933 / 1000000000) : ℝ) ≤ Real.exp (3 * (818601049 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (818601049 / 250000000) / 16) (1847716933 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1637253783 / 500000000) : ℝ) / 16) ≤ (923876373 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1637253783 / 500000000) / 16) (923876373 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((53 / 2560) : ℝ) (663 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (818601049 / 250000000) (1637253783 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (53 / 2560) (663 / 32000) (260568860987 / 250000000000) (208461603113 / 200000000000) (818601049 / 250000000) (1637253783 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (53 / 2560) (663 / 32000) (818601049 / 250000000) (1637253783 / 500000000) (54162449 / 1000000000000) (54179249 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (818601049 / 250000000) (1637253783 / 500000000) (1847716933 / 1000000000) (923876373 / 500000000) (54162449 / 1000000000000) (54179249 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0077 :
    ∀ t ∈ Set.Icc ((663 / 32000) : ℝ) (1327 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((260577003891 / 250000000000) : ℝ) ≤ Real.exp (2 * (663 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (663 / 32000)) (260577003891 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1327 / 64000) : ℝ)) ≤ (5211702941 / 5000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1327 / 64000)) (5211702941 / 5000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((28871131 / 15625000) : ℝ) ≤ Real.exp (3 * (3274506523 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3274506523 / 1000000000) / 16) (28871131 / 15625000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((409326237 / 125000000) : ℝ) / 16) ≤ (1847788199 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (409326237 / 125000000) / 16) (1847788199 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((663 / 32000) : ℝ) (1327 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3274506523 / 1000000000) (409326237 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (663 / 32000) (1327 / 64000) (260577003891 / 250000000000) (5211702941 / 5000000000) (3274506523 / 1000000000) (409326237 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (663 / 32000) (1327 / 64000) (3274506523 / 1000000000) (409326237 / 125000000) (1692057 / 31250000000) (2708131 / 50000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3274506523 / 1000000000) (409326237 / 125000000) (28871131 / 15625000) (1847788199 / 1000000000) (1692057 / 31250000000) (2708131 / 50000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0078 :
    ∀ t ∈ Set.Icc ((1327 / 64000) : ℝ) (83 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1042340588199 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1327 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1327 / 64000)) (1042340588199 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((83 / 4000) : ℝ)) ≤ (260593290463 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (83 / 4000)) (260593290463 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1847787837 / 1000000000) : ℝ) ≤ Real.exp (3 * (3274608853 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3274608853 / 1000000000) / 16) (1847787837 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3274712229 / 1000000000) : ℝ) / 16) ≤ (923911827 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3274712229 / 1000000000) / 16) (923911827 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1327 / 64000) : ℝ) (83 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3274608853 / 1000000000) (3274712229 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1327 / 64000) (83 / 4000) (1042340588199 / 1000000000000) (260593290463 / 250000000000) (3274608853 / 1000000000) (3274712229 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1327 / 64000) (83 / 4000) (3274608853 / 1000000000) (3274712229 / 1000000000) (13532301 / 250000000000) (10829199 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3274608853 / 1000000000) (3274712229 / 1000000000) (1847787837 / 1000000000) (923911827 / 500000000) (13532301 / 250000000000) (10829199 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0079 :
    ∀ t ∈ Set.Icc ((83 / 4000) : ℝ) (1329 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1042373161851 / 1000000000000) : ℝ) ≤ Real.exp (2 * (83 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (83 / 4000)) (1042373161851 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1329 / 64000) : ℝ)) ≤ (521202868261 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1329 / 64000)) (521202868261 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1847823291 / 1000000000) : ℝ) ≤ Real.exp (3 * (1637355593 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1637355593 / 500000000) / 16) (1847823291 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1637407283 / 500000000) : ℝ) / 16) ≤ (184785911 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1637407283 / 500000000) / 16) (184785911 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((83 / 4000) : ℝ) (1329 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1637355593 / 500000000) (1637407283 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (83 / 4000) (1329 / 64000) (1042373161851 / 1000000000000) (521202868261 / 500000000000) (1637355593 / 500000000) (1637407283 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (83 / 4000) (1329 / 64000) (1637355593 / 500000000) (1637407283 / 500000000) (54112589 / 1000000000000) (86607 / 1600000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1637355593 / 500000000) (1637407283 / 500000000) (1847823291 / 1000000000) (184785911 / 100000000) (54112589 / 1000000000000) (86607 / 1600000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch003 :
    ∀ t ∈ Set.Icc ((131 / 6400) : ℝ) (1329 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0060
      hpThetaDensityTwoTermCompact_cell0061)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0062
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0063
      hpThetaDensityTwoTermCompact_cell0064)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0065
      hpThetaDensityTwoTermCompact_cell0066)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0067
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0068
      hpThetaDensityTwoTermCompact_cell0069))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0070
      hpThetaDensityTwoTermCompact_cell0071)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0072
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0073
      hpThetaDensityTwoTermCompact_cell0074)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0075
      hpThetaDensityTwoTermCompact_cell0076)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0077
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0078
      hpThetaDensityTwoTermCompact_cell0079)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch003
end HodgeProofHP
