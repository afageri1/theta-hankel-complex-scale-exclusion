/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0480 :
    ∀ t ∈ Set.Icc ((361 / 12800) : ℝ) (1807 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1058027420079 / 1000000000000) : ℝ) ≤ Real.exp (2 * (361 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (361 / 12800)) (1058027420079 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1807 / 64000) : ℝ)) ≤ (1058093548861 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1807 / 64000)) (1058093548861 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((58279409 / 31250000) : ℝ) ≤ Real.exp (3 * (1661945239 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1661945239 / 500000000) / 16) (58279409 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3324099287 / 1000000000) : ℝ) / 16) ≤ (932507053 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3324099287 / 1000000000) / 16) (932507053 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((361 / 12800) : ℝ) (1807 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1661945239 / 500000000) (3324099287 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (361 / 12800) (1807 / 64000) (1058027420079 / 1000000000000) (1058093548861 / 1000000000000) (1661945239 / 500000000) (3324099287 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (361 / 12800) (1807 / 64000) (1661945239 / 500000000) (3324099287 / 1000000000) (23337593 / 500000000000) (9340887 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1661945239 / 500000000) (3324099287 / 1000000000) (58279409 / 31250000) (932507053 / 500000000) (23337593 / 500000000000) (9340887 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0481 :
    ∀ t ∈ Set.Icc ((1807 / 64000) : ℝ) (1809 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((52904677443 / 50000000000) : ℝ) ≤ Real.exp (2 * (1807 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1807 / 64000)) (52904677443 / 50000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1809 / 64000) : ℝ)) ≤ (529079840887 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1809 / 64000)) (529079840887 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((373002747 / 200000000) : ℝ) ≤ Real.exp (3 * (831024557 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (831024557 / 250000000) / 16) (373002747 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((66486141 / 20000000) : ℝ) / 16) ≤ (46627169 / 25000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (66486141 / 20000000) / 16) (46627169 / 25000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1807 / 64000) : ℝ) (1809 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (831024557 / 250000000) (66486141 / 20000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1807 / 64000) (1809 / 64000) (52904677443 / 50000000000) (529079840887 / 500000000000) (831024557 / 250000000) (66486141 / 20000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1807 / 64000) (1809 / 64000) (831024557 / 250000000) (66486141 / 20000000) (46646103 / 1000000000000) (5834417 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (831024557 / 250000000) (66486141 / 20000000) (373002747 / 200000000) (46627169 / 25000000) (46646103 / 1000000000000) (5834417 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0482 :
    ∀ t ∈ Set.Icc ((1809 / 64000) : ℝ) (1811 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1058159681773 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1809 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1809 / 64000)) (1058159681773 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1811 / 64000) : ℝ)) ≤ (1058225818821 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1811 / 64000)) (1058225818821 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((466271597 / 250000000) : ℝ) ≤ Real.exp (3 * (332430599 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (332430599 / 100000000) / 16) (466271597 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((132980593 / 40000000) : ℝ) / 16) ≤ (1865159421 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (132980593 / 40000000) / 16) (1865159421 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1809 / 64000) : ℝ) (1811 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (332430599 / 100000000) (132980593 / 40000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1809 / 64000) (1811 / 64000) (1058159681773 / 1000000000000) (1058225818821 / 1000000000000) (332430599 / 100000000) (132980593 / 40000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1809 / 64000) (1811 / 64000) (332430599 / 100000000) (132980593 / 40000000) (46617037 / 1000000000000) (46646253 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (332430599 / 100000000) (132980593 / 40000000) (466271597 / 250000000) (1865159421 / 1000000000) (46617037 / 1000000000000) (46646253 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0483 :
    ∀ t ∈ Set.Icc ((1811 / 64000) : ℝ) (1813 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((52911290941 / 50000000000) : ℝ) ≤ Real.exp (2 * (1811 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1811 / 64000)) (52911290941 / 50000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1813 / 64000) : ℝ)) ≤ (529145980001 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1813 / 64000)) (529145980001 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((37303181 / 20000000) : ℝ) ≤ Real.exp (3 * (1662256883 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1662256883 / 500000000) / 16) (37303181 / 20000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1662361307 / 500000000) : ℝ) / 16) ≤ (186523209 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1662361307 / 500000000) / 16) (186523209 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1811 / 64000) : ℝ) (1813 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1662256883 / 500000000) (1662361307 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1811 / 64000) (1813 / 64000) (52911290941 / 50000000000) (529145980001 / 500000000000) (1662256883 / 500000000) (1662361307 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1811 / 64000) (1813 / 64000) (1662256883 / 500000000) (1662361307 / 500000000) (23293993 / 500000000000) (23308593 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1662256883 / 500000000) (1662361307 / 500000000) (37303181 / 20000000) (186523209 / 100000000) (23293993 / 500000000000) (23308593 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0484 :
    ∀ t ∈ Set.Icc ((1813 / 64000) : ℝ) (363 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1058291960001 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1813 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1813 / 64000)) (1058291960001 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((363 / 12800) : ℝ)) ≤ (264589526329 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (363 / 12800)) (264589526329 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1865231719 / 1000000000) : ℝ) ≤ Real.exp (3 * (664944311 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (664944311 / 200000000) / 16) (1865231719 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((207808151 / 62500000) : ℝ) / 16) ≤ (932652383 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (207808151 / 62500000) / 16) (932652383 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1813 / 64000) : ℝ) (363 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (664944311 / 200000000) (207808151 / 62500000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1813 / 64000) (363 / 12800) (1058291960001 / 1000000000000) (264589526329 / 250000000000) (664944311 / 200000000) (207808151 / 62500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1813 / 64000) (363 / 12800) (664944311 / 200000000) (207808151 / 62500000) (5819869 / 125000000000) (9317627 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (664944311 / 200000000) (207808151 / 62500000) (1865231719 / 1000000000) (932652383 / 500000000) (5819869 / 125000000000) (9317627 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0485 :
    ∀ t ∈ Set.Icc ((363 / 12800) : ℝ) (1817 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((211671621063 / 200000000000) : ℝ) ≤ Real.exp (2 * (363 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (363 / 12800)) (211671621063 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1817 / 64000) : ℝ)) ≤ (211684850953 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1817 / 64000)) (211684850953 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((932652197 / 500000000) : ℝ) ≤ Real.exp (3 * (831232339 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (831232339 / 250000000) / 16) (932652197 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((332513823 / 100000000) : ℝ) / 16) ≤ (1865377449 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (332513823 / 100000000) / 16) (1865377449 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((363 / 12800) : ℝ) (1817 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (831232339 / 250000000) (332513823 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (363 / 12800) (1817 / 64000) (211671621063 / 200000000000) (211684850953 / 200000000000) (831232339 / 250000000) (332513823 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (363 / 12800) (1817 / 64000) (831232339 / 250000000) (332513823 / 100000000) (23264967 / 500000000000) (23279551 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (831232339 / 250000000) (332513823 / 100000000) (932652197 / 500000000) (1865377449 / 1000000000) (23264967 / 500000000000) (23279551 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0486 :
    ∀ t ∈ Set.Icc ((1817 / 64000) : ℝ) (1819 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((264606063691 / 250000000000) : ℝ) ≤ Real.exp (2 * (1817 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1817 / 64000)) (264606063691 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1819 / 64000) : ℝ)) ≤ (264622602087 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1819 / 64000)) (264622602087 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((932688539 / 500000000) : ℝ) ≤ Real.exp (3 * (3325137171 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3325137171 / 1000000000) / 16) (932688539 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1662673029 / 500000000) : ℝ) / 16) ≤ (93272507 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1662673029 / 500000000) / 16) (93272507 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1817 / 64000) : ℝ) (1819 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3325137171 / 1000000000) (1662673029 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1817 / 64000) (1819 / 64000) (264606063691 / 250000000000) (264622602087 / 250000000000) (3325137171 / 1000000000) (1662673029 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1817 / 64000) (1819 / 64000) (3325137171 / 1000000000) (1662673029 / 500000000) (46500933 / 1000000000000) (11632521 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3325137171 / 1000000000) (1662673029 / 500000000) (932688539 / 500000000) (93272507 / 50000000) (46500933 / 1000000000000) (11632521 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0487 :
    ∀ t ∈ Set.Icc ((1819 / 64000) : ℝ) (1821 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1058490408347 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1819 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1819 / 64000)) (1058490408347 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1821 / 64000) : ℝ)) ≤ (529278283033 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1821 / 64000)) (529278283033 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1865449769 / 1000000000) : ℝ) ≤ Real.exp (3 * (1662672499 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1662672499 / 500000000) / 16) (1865449769 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3325553899 / 1000000000) : ℝ) / 16) ≤ (1865522839 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3325553899 / 1000000000) / 16) (1865522839 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1819 / 64000) : ℝ) (1821 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1662672499 / 500000000) (3325553899 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1819 / 64000) (1821 / 64000) (1058490408347 / 1000000000000) (529278283033 / 500000000000) (1662672499 / 500000000) (3325553899 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1819 / 64000) (1821 / 64000) (1662672499 / 500000000) (3325553899 / 1000000000) (46471947 / 1000000000000) (23250541 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1662672499 / 500000000) (3325553899 / 1000000000) (1865449769 / 1000000000) (1865522839 / 1000000000) (46471947 / 1000000000000) (23250541 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0488 :
    ∀ t ∈ Set.Icc ((1821 / 64000) : ℝ) (1823 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((211711313213 / 200000000000) : ℝ) ≤ Real.exp (2 * (1821 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1821 / 64000)) (211711313213 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1823 / 64000) : ℝ)) ≤ (1058622727919 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1823 / 64000)) (1058622727919 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1865522467 / 1000000000) : ℝ) ≤ Real.exp (3 * (3325552839 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3325552839 / 1000000000) / 16) (1865522467 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((415720219 / 125000000) : ℝ) / 16) ≤ (233199443 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (415720219 / 125000000) / 16) (233199443 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1821 / 64000) : ℝ) (1823 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3325552839 / 1000000000) (415720219 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1821 / 64000) (1823 / 64000) (211711313213 / 200000000000) (1058622727919 / 1000000000000) (3325552839 / 1000000000) (415720219 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1821 / 64000) (1823 / 64000) (3325552839 / 1000000000) (415720219 / 125000000) (23221489 / 500000000000) (1452253 / 31250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3325552839 / 1000000000) (415720219 / 125000000) (1865522467 / 1000000000) (233199443 / 125000000) (23221489 / 500000000000) (1452253 / 31250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0489 :
    ∀ t ∈ Set.Icc ((1823 / 64000) : ℝ) (73 / 2560), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((529311363959 / 500000000000) : ℝ) ≤ Real.exp (2 * (1823 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1823 / 64000)) (529311363959 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((73 / 2560) : ℝ)) ≤ (1058688893907 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (73 / 2560)) (1058688893907 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1865595173 / 1000000000) : ℝ) ≤ Real.exp (3 * (3325760693 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3325760693 / 1000000000) / 16) (1865595173 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3325969619 / 1000000000) : ℝ) / 16) ≤ (1865668257 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3325969619 / 1000000000) / 16) (1865668257 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1823 / 64000) : ℝ) (73 / 2560),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3325760693 / 1000000000) (3325969619 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1823 / 64000) (73 / 2560) (529311363959 / 500000000000) (1058688893907 / 1000000000000) (3325760693 / 1000000000) (3325969619 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1823 / 64000) (73 / 2560) (3325760693 / 1000000000) (3325969619 / 1000000000) (23207013 / 500000000000) (46443127 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3325760693 / 1000000000) (3325969619 / 1000000000) (1865595173 / 1000000000) (1865668257 / 1000000000) (23207013 / 500000000000) (46443127 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0490 :
    ∀ t ∈ Set.Icc ((73 / 2560) : ℝ) (1827 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((529344446953 / 500000000000) : ℝ) ≤ Real.exp (2 * (73 / 2560)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (73 / 2560)) (529344446953 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1827 / 64000) : ℝ)) ≤ (1058755064031 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1827 / 64000)) (1058755064031 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((932833943 / 500000000) : ℝ) ≤ Real.exp (3 * (3325968559 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3325968559 / 1000000000) / 16) (932833943 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1663088749 / 500000000) : ℝ) / 16) ≤ (1865740977 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1663088749 / 500000000) / 16) (1865740977 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((73 / 2560) : ℝ) (1827 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3325968559 / 1000000000) (1663088749 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (73 / 2560) (1827 / 64000) (529344446953 / 500000000000) (1058755064031 / 1000000000000) (3325968559 / 1000000000) (1663088749 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (73 / 2560) (1827 / 64000) (3325968559 / 1000000000) (1663088749 / 500000000) (46385089 / 1000000000000) (23207087 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3325968559 / 1000000000) (1663088749 / 500000000) (932833943 / 500000000) (1865740977 / 1000000000) (46385089 / 1000000000000) (23207087 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0491 :
    ∀ t ∈ Set.Icc ((1827 / 64000) : ℝ) (1829 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((105875506403 / 100000000000) : ℝ) ≤ Real.exp (2 * (1827 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1827 / 64000)) (105875506403 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1829 / 64000) : ℝ)) ≤ (105882123829 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1829 / 64000)) (105882123829 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((932870303 / 500000000) : ℝ) ≤ Real.exp (3 * (3326176439 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3326176439 / 1000000000) / 16) (932870303 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3326385391 / 1000000000) : ℝ) / 16) ≤ (373162741 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3326385391 / 1000000000) / 16) (373162741 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1827 / 64000) : ℝ) (1829 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3326176439 / 1000000000) (3326385391 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1827 / 64000) (1829 / 64000) (105875506403 / 100000000000) (105882123829 / 100000000000) (3326176439 / 1000000000) (3326385391 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1827 / 64000) (1829 / 64000) (3326176439 / 1000000000) (3326385391 / 1000000000) (46356169 / 1000000000000) (23192619 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3326176439 / 1000000000) (3326385391 / 1000000000) (932870303 / 500000000) (373162741 / 200000000) (46356169 / 1000000000000) (23192619 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0492 :
    ∀ t ∈ Set.Icc ((1829 / 64000) : ℝ) (1831 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1058821238289 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1829 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1829 / 64000)) (1058821238289 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1831 / 64000) : ℝ)) ≤ (529443708343 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1831 / 64000)) (529443708343 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((932906667 / 500000000) : ℝ) ≤ Real.exp (3 * (3326384331 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3326384331 / 1000000000) / 16) (932906667 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3326593297 / 1000000000) : ℝ) / 16) ≤ (1865886441 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3326593297 / 1000000000) / 16) (1865886441 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1829 / 64000) : ℝ) (1831 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3326384331 / 1000000000) (3326593297 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1829 / 64000) (1831 / 64000) (1058821238289 / 1000000000000) (529443708343 / 500000000000) (3326384331 / 1000000000) (3326593297 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1829 / 64000) (1831 / 64000) (3326384331 / 1000000000) (3326593297 / 1000000000) (1447727 / 31250000000) (46356317 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3326384331 / 1000000000) (3326593297 / 1000000000) (932906667 / 500000000) (1865886441 / 1000000000) (1447727 / 31250000000) (46356317 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0493 :
    ∀ t ∈ Set.Icc ((1831 / 64000) : ℝ) (1833 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((211777483337 / 200000000000) : ℝ) ≤ Real.exp (2 * (1831 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1831 / 64000)) (211777483337 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1833 / 64000) : ℝ)) ≤ (1058953599217 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1833 / 64000)) (1058953599217 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1865886069 / 1000000000) : ℝ) ≤ Real.exp (3 * (3326592237 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3326592237 / 1000000000) / 16) (1865886069 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((665360243 / 200000000) : ℝ) / 16) ≤ (1865959183 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (665360243 / 200000000) / 16) (1865959183 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1831 / 64000) : ℝ) (1833 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3326592237 / 1000000000) (665360243 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1831 / 64000) (1833 / 64000) (211777483337 / 200000000000) (1058953599217 / 1000000000000) (3326592237 / 1000000000) (665360243 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1831 / 64000) (1833 / 64000) (3326592237 / 1000000000) (665360243 / 200000000) (46298377 / 1000000000000) (46327413 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3326592237 / 1000000000) (665360243 / 200000000) (1865886069 / 1000000000) (1865959183 / 1000000000) (46298377 / 1000000000000) (46327413 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0494 :
    ∀ t ∈ Set.Icc ((1833 / 64000) : ℝ) (367 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((66184599951 / 62500000000) : ℝ) ≤ Real.exp (2 * (1833 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1833 / 64000)) (66184599951 / 62500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((367 / 12800) : ℝ)) ≤ (529509892943 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (367 / 12800)) (529509892943 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1865958811 / 1000000000) : ℝ) ≤ Real.exp (3 * (665360031 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (665360031 / 200000000) / 16) (1865958811 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3327009147 / 1000000000) : ℝ) / 16) ≤ (1866031933 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3327009147 / 1000000000) / 16) (1866031933 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1833 / 64000) : ℝ) (367 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (665360031 / 200000000) (3327009147 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1833 / 64000) (367 / 12800) (66184599951 / 62500000000) (529509892943 / 500000000000) (665360031 / 200000000) (3327009147 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1833 / 64000) (367 / 12800) (665360031 / 200000000) (3327009147 / 1000000000) (9253901 / 200000000000) (1851941 / 40000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (665360031 / 200000000) (3327009147 / 1000000000) (1865958811 / 1000000000) (1866031933 / 1000000000) (9253901 / 200000000000) (1851941 / 40000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0495 :
    ∀ t ∈ Set.Icc ((367 / 12800) : ℝ) (1837 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((211803957177 / 200000000000) : ℝ) ≤ Real.exp (2 * (367 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (367 / 12800)) (211803957177 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1837 / 64000) : ℝ)) ≤ (1059085976691 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1837 / 64000)) (1059085976691 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1866031561 / 1000000000) : ℝ) ≤ Real.exp (3 * (3327008087 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3327008087 / 1000000000) / 16) (1866031561 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3327217091 / 1000000000) : ℝ) / 16) ≤ (186610469 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3327217091 / 1000000000) / 16) (186610469 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((367 / 12800) : ℝ) (1837 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3327008087 / 1000000000) (3327217091 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (367 / 12800) (1837 / 64000) (211803957177 / 200000000000) (1059085976691 / 1000000000000) (3327008087 / 1000000000) (3327217091 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (367 / 12800) (1837 / 64000) (3327008087 / 1000000000) (3327217091 / 1000000000) (46240649 / 1000000000000) (46269653 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3327008087 / 1000000000) (3327217091 / 1000000000) (1866031561 / 1000000000) (186610469 / 100000000) (46240649 / 1000000000000) (46269653 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0496 :
    ∀ t ∈ Set.Icc ((1837 / 64000) : ℝ) (1839 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((105908597669 / 100000000000) : ℝ) ≤ Real.exp (2 * (1837 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1837 / 64000)) (105908597669 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1839 / 64000) : ℝ)) ≤ (1059152171633 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1839 / 64000)) (1059152171633 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((933052159 / 500000000) : ℝ) ≤ Real.exp (3 * (3327216031 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3327216031 / 1000000000) / 16) (933052159 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3327425049 / 1000000000) : ℝ) / 16) ≤ (373235491 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3327425049 / 1000000000) / 16) (373235491 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1837 / 64000) : ℝ) (1839 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3327216031 / 1000000000) (3327425049 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1837 / 64000) (1839 / 64000) (105908597669 / 100000000000) (1059152171633 / 1000000000000) (3327216031 / 1000000000) (3327425049 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1837 / 64000) (1839 / 64000) (3327216031 / 1000000000) (3327425049 / 1000000000) (4621181 / 100000000000) (23120399 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3327216031 / 1000000000) (3327425049 / 1000000000) (933052159 / 500000000) (373235491 / 200000000) (4621181 / 100000000000) (23120399 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0497 :
    ∀ t ∈ Set.Icc ((1839 / 64000) : ℝ) (1841 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((66197010727 / 62500000000) : ℝ) ≤ Real.exp (2 * (1839 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1839 / 64000)) (66197010727 / 62500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1841 / 64000) : ℝ)) ≤ (132402296339 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1841 / 64000)) (132402296339 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1866177083 / 1000000000) : ℝ) ≤ Real.exp (3 * (3327423989 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3327423989 / 1000000000) / 16) (1866177083 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3327633019 / 1000000000) : ℝ) / 16) ≤ (1866250227 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3327633019 / 1000000000) / 16) (1866250227 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1839 / 64000) : ℝ) (1841 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3327423989 / 1000000000) (3327633019 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1839 / 64000) (1841 / 64000) (66197010727 / 62500000000) (132402296339 / 125000000000) (3327423989 / 1000000000) (3327633019 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1839 / 64000) (1841 / 64000) (3327423989 / 1000000000) (3327633019 / 1000000000) (46182987 / 1000000000000) (23105979 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3327423989 / 1000000000) (3327633019 / 1000000000) (1866177083 / 1000000000) (1866250227 / 1000000000) (46182987 / 1000000000000) (23105979 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0498 :
    ∀ t ∈ Set.Icc ((1841 / 64000) : ℝ) (1843 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1059218370711 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1841 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1841 / 64000)) (1059218370711 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1843 / 64000) : ℝ)) ≤ (1059284573929 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1843 / 64000)) (1059284573929 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((373249971 / 200000000) : ℝ) ≤ Real.exp (3 * (3327631959 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3327631959 / 1000000000) / 16) (373249971 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3327841003 / 1000000000) : ℝ) / 16) ≤ (933161503 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3327841003 / 1000000000) / 16) (933161503 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1841 / 64000) : ℝ) (1843 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3327631959 / 1000000000) (3327841003 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1841 / 64000) (1843 / 64000) (1059218370711 / 1000000000000) (1059284573929 / 1000000000000) (3327631959 / 1000000000) (3327841003 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1841 / 64000) (1843 / 64000) (3327631959 / 1000000000) (3327841003 / 1000000000) (2307709 / 50000000000) (9236627 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3327631959 / 1000000000) (3327841003 / 1000000000) (373249971 / 200000000) (933161503 / 500000000) (2307709 / 50000000000) (9236627 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0499 :
    ∀ t ∈ Set.Icc ((1843 / 64000) : ℝ) (369 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((132410571741 / 125000000000) : ℝ) ≤ Real.exp (2 * (1843 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1843 / 64000)) (132410571741 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((369 / 12800) : ℝ)) ≤ (264837695321 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (369 / 12800)) (264837695321 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((933161317 / 500000000) : ℝ) ≤ Real.exp (3 * (3327839943 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3327839943 / 1000000000) / 16) (933161317 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3328049 / 1000000) : ℝ) / 16) ≤ (1866395793 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3328049 / 1000000) / 16) (1866395793 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1843 / 64000) : ℝ) (369 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3327839943 / 1000000000) (3328049 / 1000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1843 / 64000) (369 / 12800) (132410571741 / 125000000000) (264837695321 / 250000000000) (3327839943 / 1000000000) (3328049 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1843 / 64000) (369 / 12800) (3327839943 / 1000000000) (3328049 / 1000000) (46125389 / 1000000000000) (5769291 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3327839943 / 1000000000) (3328049 / 1000000) (933161317 / 500000000) (1866395793 / 1000000000) (46125389 / 1000000000000) (5769291 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch024 :
    ∀ t ∈ Set.Icc ((361 / 12800) : ℝ) (369 / 12800),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0480
      hpThetaDensityTwoTermCompact_cell0481)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0482
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0483
      hpThetaDensityTwoTermCompact_cell0484)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0485
      hpThetaDensityTwoTermCompact_cell0486)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0487
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0488
      hpThetaDensityTwoTermCompact_cell0489))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0490
      hpThetaDensityTwoTermCompact_cell0491)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0492
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0493
      hpThetaDensityTwoTermCompact_cell0494)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0495
      hpThetaDensityTwoTermCompact_cell0496)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0497
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0498
      hpThetaDensityTwoTermCompact_cell0499)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch024
end HodgeProofHP
