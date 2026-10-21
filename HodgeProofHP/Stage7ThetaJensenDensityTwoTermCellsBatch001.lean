/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0020 :
    ∀ t ∈ Set.Icc ((129 / 6400) : ℝ) (2581 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((208227215677 / 200000000000) : ℝ) ≤ Real.exp (2 * (129 / 6400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (129 / 6400)) (208227215677 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2581 / 128000) : ℝ)) ≤ (130144043283 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2581 / 128000)) (130144043283 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1846477269 / 1000000000) : ℝ) ≤ Real.exp (3 * (1635412387 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1635412387 / 500000000) / 16) (1846477269 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3270876923 / 1000000000) : ℝ) / 16) ≤ (73859813 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3270876923 / 1000000000) / 16) (73859813 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((129 / 6400) : ℝ) (2581 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1635412387 / 500000000) (3270876923 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (129 / 6400) (2581 / 128000) (208227215677 / 200000000000) (130144043283 / 125000000000) (1635412387 / 500000000) (3270876923 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (129 / 6400) (2581 / 128000) (1635412387 / 500000000) (3270876923 / 1000000000) (54755607 / 1000000000000) (2190567 / 40000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1635412387 / 500000000) (3270876923 / 1000000000) (1846477269 / 1000000000) (73859813 / 40000000) (54755607 / 1000000000000) (2190567 / 40000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0021 :
    ∀ t ∈ Set.Icc ((2581 / 128000) : ℝ) (1291 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1041152346263 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2581 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2581 / 128000)) (1041152346263 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1291 / 64000) : ℝ)) ≤ (1041168614397 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1291 / 64000)) (1041168614397 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1846494963 / 1000000000) : ℝ) ≤ Real.exp (3 * (3270875881 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3270875881 / 1000000000) / 16) (1846494963 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3270928031 / 1000000000) : ℝ) / 16) ≤ (1846513019 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3270928031 / 1000000000) / 16) (1846513019 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2581 / 128000) : ℝ) (1291 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3270875881 / 1000000000) (3270928031 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2581 / 128000) (1291 / 64000) (1041152346263 / 1000000000000) (1041168614397 / 1000000000000) (3270875881 / 1000000000) (3270928031 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2581 / 128000) (1291 / 64000) (3270875881 / 1000000000) (3270928031 / 1000000000) (13686803 / 250000000000) (2737789 / 50000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3270875881 / 1000000000) (3270928031 / 1000000000) (1846494963 / 1000000000) (1846513019 / 1000000000) (13686803 / 250000000000) (2737789 / 50000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0022 :
    ∀ t ∈ Set.Icc ((1291 / 64000) : ℝ) (2583 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((260292153599 / 250000000000) : ℝ) ≤ Real.exp (2 * (1291 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1291 / 64000)) (260292153599 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2583 / 128000) : ℝ)) ≤ (1041184882783 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2583 / 128000)) (1041184882783 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((923256329 / 500000000) : ℝ) ≤ Real.exp (3 * (3270926989 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3270926989 / 1000000000) / 16) (923256329 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((163548957 / 50000000) : ℝ) / 16) ≤ (923265357 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (163548957 / 50000000) / 16) (923265357 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1291 / 64000) : ℝ) (2583 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3270926989 / 1000000000) (163548957 / 50000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1291 / 64000) (2583 / 128000) (260292153599 / 250000000000) (1041184882783 / 1000000000000) (3270926989 / 1000000000) (163548957 / 50000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1291 / 64000) (2583 / 128000) (3270926989 / 1000000000) (163548957 / 50000000) (54738819 / 1000000000000) (10949477 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3270926989 / 1000000000) (163548957 / 50000000) (923256329 / 500000000) (923265357 / 500000000) (54738819 / 1000000000000) (10949477 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0023 :
    ∀ t ∈ Set.Icc ((2583 / 128000) : ℝ) (323 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((520592441391 / 500000000000) : ℝ) ≤ Real.exp (2 * (2583 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2583 / 128000)) (520592441391 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((323 / 16000) : ℝ)) ≤ (16268767991 / 15625000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (323 / 16000)) (16268767991 / 15625000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1846530353 / 1000000000) : ℝ) ≤ Real.exp (3 * (1635489049 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1635489049 / 500000000) / 16) (1846530353 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3271030249 / 1000000000) : ℝ) / 16) ≤ (184654841 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3271030249 / 1000000000) / 16) (184654841 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2583 / 128000) : ℝ) (323 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1635489049 / 500000000) (3271030249 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2583 / 128000) (323 / 16000) (520592441391 / 500000000000) (16268767991 / 15625000000) (1635489049 / 500000000) (3271030249 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2583 / 128000) (323 / 16000) (1635489049 / 500000000) (3271030249 / 1000000000) (27365213 / 500000000000) (54738991 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1635489049 / 500000000) (3271030249 / 1000000000) (1846530353 / 1000000000) (184654841 / 100000000) (27365213 / 500000000000) (54738991 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0024 :
    ∀ t ∈ Set.Icc ((323 / 16000) : ℝ) (517 / 25600), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1041201151423 / 1000000000000) : ℝ) ≤ Real.exp (2 * (323 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (323 / 16000)) (1041201151423 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((517 / 25600) : ℝ)) ≤ (1041217420319 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (517 / 25600)) (1041217420319 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((115409253 / 62500000) : ℝ) ≤ Real.exp (3 * (3271029207 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3271029207 / 1000000000) / 16) (115409253 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((40888517 / 12500000) : ℝ) / 16) ≤ (923283053 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (40888517 / 12500000) / 16) (923283053 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((323 / 16000) : ℝ) (517 / 25600),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3271029207 / 1000000000) (40888517 / 12500000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (323 / 16000) (517 / 25600) (1041201151423 / 1000000000000) (1041217420319 / 1000000000000) (3271029207 / 1000000000) (40888517 / 12500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (323 / 16000) (517 / 25600) (3271029207 / 1000000000) (40888517 / 12500000) (10944407 / 200000000000) (54730599 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3271029207 / 1000000000) (40888517 / 12500000) (115409253 / 62500000) (923283053 / 500000000) (10944407 / 200000000000) (54730599 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0025 :
    ∀ t ∈ Set.Icc ((517 / 25600) : ℝ) (1293 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((520608710159 / 500000000000) : ℝ) ≤ Real.exp (2 * (517 / 25600)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (517 / 25600)) (520608710159 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1293 / 64000) : ℝ)) ≤ (1041233689469 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1293 / 64000)) (1041233689469 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((115410359 / 62500000) : ℝ) ≤ Real.exp (3 * (3271080317 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3271080317 / 1000000000) / 16) (115410359 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3271132471 / 1000000000) : ℝ) / 16) ≤ (923291901 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3271132471 / 1000000000) / 16) (923291901 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((517 / 25600) : ℝ) (1293 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3271080317 / 1000000000) (3271132471 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (517 / 25600) (1293 / 64000) (520608710159 / 500000000000) (1041233689469 / 1000000000000) (3271080317 / 1000000000) (3271132471 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (517 / 25600) (1293 / 64000) (3271080317 / 1000000000) (3271132471 / 1000000000) (10942729 / 200000000000) (1710069 / 31250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3271080317 / 1000000000) (3271132471 / 1000000000) (115410359 / 62500000) (923291901 / 500000000) (10942729 / 200000000000) (1710069 / 31250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0026 :
    ∀ t ∈ Set.Icc ((1293 / 64000) : ℝ) (2587 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((260308422367 / 250000000000) : ℝ) ≤ Real.exp (2 * (1293 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1293 / 64000)) (260308422367 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2587 / 128000) : ℝ)) ≤ (130156244859 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2587 / 128000)) (130156244859 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((23082293 / 12500000) : ℝ) ≤ Real.exp (3 * (817782857 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (817782857 / 250000000) / 16) (23082293 / 12500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3271183583 / 1000000000) : ℝ) / 16) ≤ (1846601499 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3271183583 / 1000000000) / 16) (1846601499 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1293 / 64000) : ℝ) (2587 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (817782857 / 250000000) (3271183583 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1293 / 64000) (2587 / 128000) (260308422367 / 250000000000) (130156244859 / 125000000000) (817782857 / 250000000) (3271183583 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1293 / 64000) (2587 / 128000) (817782857 / 250000000) (3271183583 / 1000000000) (6838157 / 125000000000) (27356909 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (817782857 / 250000000) (3271183583 / 1000000000) (23082293 / 12500000) (1846601499 / 1000000000) (6838157 / 125000000000) (27356909 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0027 :
    ∀ t ∈ Set.Icc ((2587 / 128000) : ℝ) (647 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1041249958871 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2587 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2587 / 128000)) (1041249958871 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((647 / 32000) : ℝ)) ≤ (104126622853 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (647 / 32000)) (104126622853 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1846601137 / 1000000000) : ℝ) ≤ Real.exp (3 * (163559127 / 50000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (163559127 / 50000000) / 16) (1846601137 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((654246939 / 200000000) : ℝ) / 16) ≤ (461654799 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (654246939 / 200000000) / 16) (461654799 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2587 / 128000) : ℝ) (647 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (163559127 / 50000000) (654246939 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2587 / 128000) (647 / 32000) (1041249958871 / 1000000000000) (104126622853 / 100000000000) (163559127 / 50000000) (654246939 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2587 / 128000) (647 / 32000) (163559127 / 50000000) (654246939 / 200000000) (13674217 / 250000000000) (54705429 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (163559127 / 50000000) (654246939 / 200000000) (1846601137 / 1000000000) (461654799 / 250000000) (13674217 / 250000000000) (54705429 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0028 :
    ∀ t ∈ Set.Icc ((647 / 32000) : ℝ) (2589 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1041266228529 / 1000000000000) : ℝ) ≤ Real.exp (2 * (647 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (647 / 32000)) (1041266228529 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2589 / 128000) : ℝ)) ≤ (520641249221 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2589 / 128000)) (520641249221 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((923309417 / 500000000) : ℝ) ≤ Real.exp (3 * (3271233653 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3271233653 / 1000000000) / 16) (923309417 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3271285809 / 1000000000) : ℝ) / 16) ≤ (923318447 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3271285809 / 1000000000) / 16) (923318447 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((647 / 32000) : ℝ) (2589 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3271233653 / 1000000000) (3271285809 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (647 / 32000) (2589 / 128000) (1041266228529 / 1000000000000) (520641249221 / 500000000000) (3271233653 / 1000000000) (3271285809 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (647 / 32000) (2589 / 128000) (3271233653 / 1000000000) (3271285809 / 1000000000) (27344241 / 500000000000) (54697041 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3271233653 / 1000000000) (3271285809 / 1000000000) (923309417 / 500000000) (923318447 / 500000000) (27344241 / 500000000000) (54697041 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0029 :
    ∀ t ∈ Set.Icc ((2589 / 128000) : ℝ) (259 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1041282498441 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2589 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2589 / 128000)) (1041282498441 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((259 / 12800) : ℝ)) ≤ (32540586519 / 31250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (259 / 12800)) (32540586519 / 31250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((461659133 / 250000000) : ℝ) ≤ Real.exp (3 * (1635642383 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1635642383 / 500000000) / 16) (461659133 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3271336923 / 1000000000) : ℝ) / 16) ≤ (14426989 / 7812500) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3271336923 / 1000000000) / 16) (14426989 / 7812500) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2589 / 128000) : ℝ) (259 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1635642383 / 500000000) (3271336923 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2589 / 128000) (259 / 12800) (1041282498441 / 1000000000000) (32540586519 / 31250000000) (1635642383 / 500000000) (3271336923 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2589 / 128000) (259 / 12800) (1635642383 / 500000000) (3271336923 / 1000000000) (1708753 / 31250000000) (27344327 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1635642383 / 500000000) (3271336923 / 1000000000) (461659133 / 250000000) (14426989 / 7812500) (1708753 / 31250000000) (27344327 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0030 :
    ∀ t ∈ Set.Icc ((259 / 12800) : ℝ) (2591 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1041298768607 / 1000000000000) : ℝ) ≤ Real.exp (2 * (259 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (259 / 12800)) (1041298768607 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2591 / 128000) : ℝ)) ≤ (260328759757 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2591 / 128000)) (260328759757 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((184665423 / 100000000) : ℝ) ≤ Real.exp (3 * (3271335881 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3271335881 / 1000000000) / 16) (184665423 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1635694019 / 500000000) : ℝ) / 16) ≤ (184667229 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1635694019 / 500000000) / 16) (184667229 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((259 / 12800) : ℝ) (2591 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3271335881 / 1000000000) (1635694019 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (259 / 12800) (2591 / 128000) (1041298768607 / 1000000000000) (260328759757 / 250000000000) (3271335881 / 1000000000) (1635694019 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (259 / 12800) (2591 / 128000) (3271335881 / 1000000000) (1635694019 / 500000000) (1708491 / 31250000000) (54680269 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3271335881 / 1000000000) (1635694019 / 500000000) (184665423 / 100000000) (184667229 / 100000000) (1708491 / 31250000000) (54680269 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0031 :
    ∀ t ∈ Set.Icc ((2591 / 128000) : ℝ) (81 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1041315039027 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2591 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2591 / 128000)) (1041315039027 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((81 / 4000) : ℝ)) ≤ (1041331309703 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (81 / 4000)) (1041331309703 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1846671929 / 1000000000) : ℝ) ≤ Real.exp (3 * (817846749 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (817846749 / 250000000) / 16) (1846671929 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1635719577 / 500000000) : ℝ) / 16) ≤ (1846689989 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1635719577 / 500000000) / 16) (1846689989 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2591 / 128000) : ℝ) (81 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (817846749 / 250000000) (1635719577 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2591 / 128000) (81 / 4000) (1041315039027 / 1000000000000) (1041331309703 / 1000000000000) (817846749 / 250000000) (1635719577 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2591 / 128000) (81 / 4000) (817846749 / 250000000) (1635719577 / 500000000) (54663329 / 1000000000000) (13667971 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (817846749 / 250000000) (1635719577 / 500000000) (1846671929 / 1000000000) (1846689989 / 1000000000) (54663329 / 1000000000000) (13667971 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0032 :
    ∀ t ∈ Set.Icc ((81 / 4000) : ℝ) (2593 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((520665654851 / 500000000000) : ℝ) ≤ Real.exp (2 * (81 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (81 / 4000)) (520665654851 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2593 / 128000) : ℝ)) ≤ (130168447579 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2593 / 128000)) (130168447579 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1846689627 / 1000000000) : ℝ) ≤ Real.exp (3 * (3271438111 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3271438111 / 1000000000) / 16) (1846689627 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((327149027 / 100000000) : ℝ) / 16) ≤ (1846707689 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (327149027 / 100000000) / 16) (1846707689 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((81 / 4000) : ℝ) (2593 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3271438111 / 1000000000) (327149027 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (81 / 4000) (2593 / 128000) (520665654851 / 500000000000) (130168447579 / 125000000000) (3271438111 / 1000000000) (327149027 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (81 / 4000) (2593 / 128000) (3271438111 / 1000000000) (327149027 / 100000000) (54654947 / 1000000000000) (27331751 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3271438111 / 1000000000) (327149027 / 100000000) (1846689627 / 1000000000) (1846707689 / 1000000000) (54654947 / 1000000000000) (27331751 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0033 :
    ∀ t ∈ Set.Icc ((2593 / 128000) : ℝ) (1297 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1041347580631 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2593 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2593 / 128000)) (1041347580631 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1297 / 64000) : ℝ)) ≤ (208272770363 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1297 / 64000)) (208272770363 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1846707327 / 1000000000) : ℝ) ≤ Real.exp (3 * (817872307 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (817872307 / 250000000) / 16) (1846707327 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((817885347 / 250000000) : ℝ) / 16) ≤ (1846725389 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (817885347 / 250000000) / 16) (1846725389 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2593 / 128000) : ℝ) (1297 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (817872307 / 250000000) (817885347 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2593 / 128000) (1297 / 64000) (1041347580631 / 1000000000000) (208272770363 / 200000000000) (817872307 / 250000000) (817885347 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2593 / 128000) (1297 / 64000) (817872307 / 250000000) (817885347 / 250000000) (27323283 / 500000000000) (54655119 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (817872307 / 250000000) (817885347 / 250000000) (1846707327 / 1000000000) (1846725389 / 1000000000) (27323283 / 500000000000) (54655119 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0034 :
    ∀ t ∈ Set.Icc ((1297 / 64000) : ℝ) (519 / 25600), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((520681925907 / 500000000000) : ℝ) ≤ Real.exp (2 * (1297 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1297 / 64000)) (520681925907 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((519 / 25600) : ℝ)) ≤ (260345030813 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (519 / 25600)) (260345030813 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1846725027 / 1000000000) : ℝ) ≤ Real.exp (3 * (654308069 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (654308069 / 200000000) / 16) (1846725027 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1635796253 / 500000000) : ℝ) / 16) ≤ (1846743089 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1635796253 / 500000000) / 16) (1846743089 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1297 / 64000) : ℝ) (519 / 25600),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (654308069 / 200000000) (1635796253 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1297 / 64000) (519 / 25600) (520681925907 / 500000000000) (260345030813 / 250000000000) (654308069 / 200000000) (1635796253 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1297 / 64000) (519 / 25600) (654308069 / 200000000) (1635796253 / 500000000) (54638187 / 1000000000000) (27323369 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (654308069 / 200000000) (1635796253 / 500000000) (1846725027 / 1000000000) (1846743089 / 1000000000) (54638187 / 1000000000000) (27323369 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0035 :
    ∀ t ∈ Set.Icc ((519 / 25600) : ℝ) (649 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1041380123251 / 1000000000000) : ℝ) ≤ Real.exp (2 * (519 / 25600)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (519 / 25600)) (1041380123251 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((649 / 32000) : ℝ)) ≤ (16271818671 / 15625000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (649 / 32000)) (16271818671 / 15625000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1846742727 / 1000000000) : ℝ) ≤ Real.exp (3 * (408948933 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (408948933 / 125000000) / 16) (1846742727 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((26173149 / 8000000) : ℝ) / 16) ≤ (184676079 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (26173149 / 8000000) / 16) (184676079 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((519 / 25600) : ℝ) (649 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (408948933 / 125000000) (26173149 / 8000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (519 / 25600) (649 / 32000) (1041380123251 / 1000000000000) (16271818671 / 15625000000) (408948933 / 125000000) (26173149 / 8000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (519 / 25600) (649 / 32000) (408948933 / 125000000) (26173149 / 8000000) (3414363 / 62500000000) (54638359 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (408948933 / 125000000) (26173149 / 8000000) (1846742727 / 1000000000) (184676079 / 100000000) (3414363 / 62500000000) (54638359 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0036 :
    ∀ t ∈ Set.Icc ((649 / 32000) : ℝ) (2597 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1041396394943 / 1000000000000) : ℝ) ≤ Real.exp (2 * (649 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (649 / 32000)) (1041396394943 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2597 / 128000) : ℝ)) ≤ (104141266689 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2597 / 128000)) (104141266689 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((461690107 / 250000000) : ℝ) ≤ Real.exp (3 * (3271642583 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3271642583 / 1000000000) / 16) (461690107 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((654338949 / 200000000) : ℝ) / 16) ≤ (1846778491 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (654338949 / 200000000) / 16) (1846778491 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((649 / 32000) : ℝ) (2597 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3271642583 / 1000000000) (654338949 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (649 / 32000) (2597 / 128000) (1041396394943 / 1000000000000) (104141266689 / 100000000000) (3271642583 / 1000000000) (654338949 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (649 / 32000) (2597 / 128000) (3271642583 / 1000000000) (654338949 / 200000000) (54621431 / 1000000000000) (2731499 / 50000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3271642583 / 1000000000) (654338949 / 200000000) (461690107 / 250000000) (1846778491 / 1000000000) (54621431 / 1000000000000) (2731499 / 50000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0037 :
    ∀ t ∈ Set.Icc ((2597 / 128000) : ℝ) (1299 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1041412666889 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2597 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2597 / 128000)) (1041412666889 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1299 / 64000) : ℝ)) ≤ (104142893909 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1299 / 64000)) (104142893909 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1846778129 / 1000000000) : ℝ) ≤ Real.exp (3 * (1635846851 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1635846851 / 500000000) / 16) (1846778129 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1635872933 / 500000000) : ℝ) / 16) ≤ (1846796193 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1635872933 / 500000000) / 16) (1846796193 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2597 / 128000) : ℝ) (1299 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1635846851 / 500000000) (1635872933 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2597 / 128000) (1299 / 64000) (1041412666889 / 1000000000000) (104142893909 / 100000000000) (1635846851 / 500000000) (1635872933 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2597 / 128000) (1299 / 64000) (1635846851 / 500000000) (1635872933 / 500000000) (27306527 / 500000000000) (54621603 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1635846851 / 500000000) (1635872933 / 500000000) (1846778129 / 1000000000) (1846796193 / 1000000000) (27306527 / 500000000000) (54621603 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0038 :
    ∀ t ∈ Set.Icc ((1299 / 64000) : ℝ) (2599 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1041428939089 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1299 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1299 / 64000)) (1041428939089 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2599 / 128000) : ℝ)) ≤ (130180651443 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2599 / 128000)) (130180651443 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1846795831 / 1000000000) : ℝ) ≤ Real.exp (3 * (3271744823 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3271744823 / 1000000000) / 16) (1846795831 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3271796987 / 1000000000) : ℝ) / 16) ≤ (369362779 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3271796987 / 1000000000) / 16) (369362779 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1299 / 64000) : ℝ) (2599 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3271744823 / 1000000000) (3271796987 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1299 / 64000) (2599 / 128000) (1041428939089 / 1000000000000) (130180651443 / 125000000000) (3271744823 / 1000000000) (3271796987 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1299 / 64000) (2599 / 128000) (3271744823 / 1000000000) (3271796987 / 1000000000) (54604679 / 1000000000000) (54613227 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3271744823 / 1000000000) (3271796987 / 1000000000) (1846795831 / 1000000000) (369362779 / 200000000) (54604679 / 1000000000000) (54613227 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0039 :
    ∀ t ∈ Set.Icc ((2599 / 128000) : ℝ) (13 / 640), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1041445211543 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2599 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2599 / 128000)) (1041445211543 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((13 / 640) : ℝ)) ≤ (260365371063 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (13 / 640)) (260365371063 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1846813533 / 1000000000) : ℝ) ≤ Real.exp (3 * (654359189 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (654359189 / 200000000) / 16) (1846813533 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3271848109 / 1000000000) : ℝ) / 16) ≤ (1846831597 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3271848109 / 1000000000) / 16) (1846831597 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2599 / 128000) : ℝ) (13 / 640),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (654359189 / 200000000) (3271848109 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2599 / 128000) (13 / 640) (1041445211543 / 1000000000000) (260365371063 / 250000000000) (654359189 / 200000000) (3271848109 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2599 / 128000) (13 / 640) (654359189 / 200000000) (3271848109 / 1000000000) (27298153 / 500000000000) (13651213 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (654359189 / 200000000) (3271848109 / 1000000000) (1846813533 / 1000000000) (1846831597 / 1000000000) (27298153 / 500000000000) (13651213 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch001 :
    ∀ t ∈ Set.Icc ((129 / 6400) : ℝ) (13 / 640),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0020
      hpThetaDensityTwoTermCompact_cell0021)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0022
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0023
      hpThetaDensityTwoTermCompact_cell0024)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0025
      hpThetaDensityTwoTermCompact_cell0026)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0027
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0028
      hpThetaDensityTwoTermCompact_cell0029))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0030
      hpThetaDensityTwoTermCompact_cell0031)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0032
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0033
      hpThetaDensityTwoTermCompact_cell0034)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0035
      hpThetaDensityTwoTermCompact_cell0036)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0037
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0038
      hpThetaDensityTwoTermCompact_cell0039)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch001
end HodgeProofHP
