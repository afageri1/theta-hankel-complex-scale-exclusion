/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0920 :
    ∀ t ∈ Set.Icc ((4131 / 64000) : ℝ) (4147 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((568898393807 / 500000000000) : ℝ) ≤ Real.exp (2 * (4131 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4131 / 64000)) (568898393807 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4147 / 64000) : ℝ)) ≤ (1138365828257 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4147 / 64000)) (1138365828257 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((390932479 / 200000000) : ℝ) ≤ Real.exp (3 * (714898657 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (714898657 / 200000000) / 16) (390932479 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1788141059 / 500000000) : ℝ) / 16) ≤ (61103691 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1788141059 / 500000000) / 16) (61103691 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4131 / 64000) : ℝ) (4147 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (714898657 / 200000000) (1788141059 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4131 / 64000) (4147 / 64000) (568898393807 / 500000000000) (1138365828257 / 1000000000000) (714898657 / 200000000) (1788141059 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4131 / 64000) (4147 / 64000) (714898657 / 200000000) (1788141059 / 500000000) (1368993 / 62500000000) (22021753 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (714898657 / 200000000) (1788141059 / 500000000) (390932479 / 200000000) (61103691 / 31250000) (1368993 / 62500000000) (22021753 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0921 :
    ∀ t ∈ Set.Icc ((4147 / 64000) : ℝ) (4163 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((35573932133 / 31250000000) : ℝ) ≤ Real.exp (2 * (4147 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4147 / 64000)) (35573932133 / 31250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4163 / 64000) : ℝ)) ≤ (1138935153491 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4163 / 64000)) (1138935153491 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1955317693 / 1000000000) : ℝ) ≤ Real.exp (3 * (3576280979 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3576280979 / 1000000000) / 16) (1955317693 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1789035353 / 500000000) : ℝ) / 16) ≤ (977986979 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1789035353 / 500000000) / 16) (977986979 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4147 / 64000) : ℝ) (4163 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3576280979 / 1000000000) (1789035353 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4147 / 64000) (4163 / 64000) (35573932133 / 31250000000) (1138935153491 / 1000000000000) (3576280979 / 1000000000) (1789035353 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4147 / 64000) (4163 / 64000) (3576280979 / 1000000000) (1789035353 / 500000000) (1361667 / 62500000000) (4380793 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3576280979 / 1000000000) (1789035353 / 500000000) (1955317693 / 1000000000) (977986979 / 500000000) (1361667 / 62500000000) (4380793 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0922 :
    ∀ t ∈ Set.Icc ((4163 / 64000) : ℝ) (4179 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((113893515349 / 100000000000) : ℝ) ≤ Real.exp (2 * (4163 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4163 / 64000)) (113893515349 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4179 / 64000) : ℝ)) ≤ (569752381729 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4179 / 64000)) (569752381729 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1955973539 / 1000000000) : ℝ) ≤ Real.exp (3 * (1789034783 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1789034783 / 500000000) / 16) (1955973539 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3579860189 / 1000000000) : ℝ) / 16) ≤ (122289397 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3579860189 / 1000000000) / 16) (122289397 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4163 / 64000) : ℝ) (4179 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1789034783 / 500000000) (3579860189 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4163 / 64000) (4179 / 64000) (113893515349 / 100000000000) (569752381729 / 500000000000) (1789034783 / 500000000) (3579860189 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4163 / 64000) (4179 / 64000) (1789034783 / 500000000) (3579860189 / 1000000000) (866801 / 40000000000) (5446687 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1789034783 / 500000000) (3579860189 / 1000000000) (1955973539 / 1000000000) (122289397 / 62500000) (866801 / 40000000000) (5446687 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0923 :
    ∀ t ∈ Set.Icc ((4179 / 64000) : ℝ) (839 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1139504763457 / 1000000000000) : ℝ) ≤ Real.exp (2 * (4179 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4179 / 64000)) (1139504763457 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((839 / 12800) : ℝ)) ≤ (570037329151 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (839 / 12800)) (570037329151 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1956629933 / 1000000000) : ℝ) ≤ Real.exp (3 * (447482381 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (447482381 / 125000000) / 16) (1956629933 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1790825283 / 500000000) : ℝ) / 16) ≤ (391457459 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1790825283 / 500000000) / 16) (391457459 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4179 / 64000) : ℝ) (839 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (447482381 / 125000000) (1790825283 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4179 / 64000) (839 / 12800) (1139504763457 / 1000000000000) (570037329151 / 500000000000) (447482381 / 125000000) (1790825283 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4179 / 64000) (839 / 12800) (447482381 / 125000000) (1790825283 / 500000000) (2694243 / 125000000000) (216701 / 10000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (447482381 / 125000000) (1790825283 / 500000000) (1956629933 / 1000000000) (391457459 / 200000000) (2694243 / 125000000000) (216701 / 10000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0924 :
    ∀ t ∈ Set.Icc ((839 / 12800) : ℝ) (4211 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1140074658301 / 1000000000000) : ℝ) ≤ Real.exp (2 * (839 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (839 / 12800)) (1140074658301 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4211 / 64000) : ℝ)) ≤ (285161209541 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4211 / 64000)) (285161209541 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((3131659 / 1600000) : ℝ) ≤ Real.exp (3 * (143265977 / 40000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (143265977 / 40000000) / 16) (3131659 / 1600000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((44793023 / 12500000) : ℝ) / 16) ≤ (1957944787 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (44793023 / 12500000) / 16) (1957944787 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((839 / 12800) : ℝ) (4211 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (143265977 / 40000000) (44793023 / 12500000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (839 / 12800) (4211 / 64000) (1140074658301 / 1000000000000) (285161209541 / 250000000000) (143265977 / 40000000) (44793023 / 12500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (839 / 12800) (4211 / 64000) (143265977 / 40000000) (44793023 / 12500000) (5359607 / 250000000000) (21554019 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (143265977 / 40000000) (44793023 / 12500000) (3131659 / 1600000) (1957944787 / 1000000000) (5359607 / 250000000000) (21554019 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0925 :
    ∀ t ∈ Set.Icc ((4211 / 64000) : ℝ) (4227 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1140644838163 / 1000000000000) : ℝ) ≤ Real.exp (2 * (4211 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4211 / 64000)) (1140644838163 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4227 / 64000) : ℝ)) ≤ (1141215303187 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4227 / 64000)) (1141215303187 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1957944367 / 1000000000) : ℝ) ≤ Real.exp (3 * (1791720349 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1791720349 / 500000000) / 16) (1957944367 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((448154251 / 125000000) : ℝ) / 16) ≤ (1958602829 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (448154251 / 125000000) / 16) (1958602829 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4211 / 64000) : ℝ) (4227 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1791720349 / 500000000) (448154251 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4211 / 64000) (4227 / 64000) (1140644838163 / 1000000000000) (1141215303187 / 1000000000000) (1791720349 / 500000000) (448154251 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4211 / 64000) (4227 / 64000) (1791720349 / 500000000) (448154251 / 125000000) (21323473 / 1000000000000) (21438503 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1791720349 / 500000000) (448154251 / 125000000) (1957944367 / 1000000000) (1958602829 / 1000000000) (21323473 / 1000000000000) (21438503 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0926 :
    ∀ t ∈ Set.Icc ((4227 / 64000) : ℝ) (4243 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((570607651593 / 500000000000) : ℝ) ≤ Real.exp (2 * (4227 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4227 / 64000)) (570607651593 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4243 / 64000) : ℝ)) ≤ (228357210703 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4243 / 64000)) (228357210703 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1958602409 / 1000000000) : ℝ) ≤ Real.exp (3 * (1792616433 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1792616433 / 500000000) / 16) (1958602409 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1793513537 / 500000000) : ℝ) / 16) ≤ (979630711 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1793513537 / 500000000) / 16) (979630711 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4227 / 64000) : ℝ) (4243 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1792616433 / 500000000) (1793513537 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4227 / 64000) (4243 / 64000) (570607651593 / 500000000000) (228357210703 / 200000000000) (1792616433 / 500000000) (1793513537 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4227 / 64000) (4243 / 64000) (1792616433 / 500000000) (1793513537 / 500000000) (10604539 / 500000000000) (5330887 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1792616433 / 500000000) (1793513537 / 500000000) (1958602409 / 1000000000) (979630711 / 500000000) (10604539 / 500000000000) (5330887 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0927 :
    ∀ t ∈ Set.Icc ((4243 / 64000) : ℝ) (4259 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((570893026757 / 500000000000) : ℝ) ≤ Real.exp (2 * (4243 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4243 / 64000)) (570893026757 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4259 / 64000) : ℝ)) ≤ (1142357089289 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4259 / 64000)) (1142357089289 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1959261001 / 1000000000) : ℝ) ≤ Real.exp (3 * (3587025931 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3587025931 / 1000000000) / 16) (1959261001 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((897205259 / 250000000) : ℝ) / 16) ≤ (391984113 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (897205259 / 250000000) / 16) (391984113 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4243 / 64000) : ℝ) (4259 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3587025931 / 1000000000) (897205259 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4243 / 64000) (4259 / 64000) (570893026757 / 500000000000) (1142357089289 / 1000000000000) (3587025931 / 1000000000) (897205259 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4243 / 64000) (4259 / 64000) (3587025931 / 1000000000) (897205259 / 250000000) (527381 / 25000000000) (331393 / 15625000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3587025931 / 1000000000) (897205259 / 250000000) (1959261001 / 1000000000) (391984113 / 200000000) (527381 / 25000000000) (331393 / 15625000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0928 :
    ∀ t ∈ Set.Icc ((4259 / 64000) : ℝ) (171 / 2560), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((142794636161 / 125000000000) : ℝ) ≤ Real.exp (2 * (4259 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4259 / 64000)) (142794636161 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((171 / 2560) : ℝ)) ≤ (285732102663 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (171 / 2560)) (285732102663 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((122495009 / 62500000) : ℝ) ≤ Real.exp (3 * (897204973 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (897204973 / 250000000) / 16) (122495009 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((718123179 / 200000000) : ℝ) / 16) ≤ (98029013 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (718123179 / 200000000) / 16) (98029013 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4259 / 64000) : ℝ) (171 / 2560),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (897204973 / 250000000) (718123179 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4259 / 64000) (171 / 2560) (142794636161 / 125000000000) (285732102663 / 250000000000) (897204973 / 250000000) (718123179 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4259 / 64000) (171 / 2560) (897204973 / 250000000) (718123179 / 200000000) (5245489 / 250000000000) (10547657 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (897204973 / 250000000) (718123179 / 200000000) (122495009 / 62500000) (98029013 / 50000000) (5245489 / 250000000000) (10547657 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0929 :
    ∀ t ∈ Set.Icc ((171 / 2560) : ℝ) (4291 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1142928410651 / 1000000000000) : ℝ) ≤ Real.exp (2 * (171 / 2560)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (171 / 2560)) (1142928410651 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4291 / 64000) : ℝ)) ≤ (1143500017747 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4291 / 64000)) (1143500017747 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1960579839 / 1000000000) : ℝ) ≤ Real.exp (3 * (3590614751 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3590614751 / 1000000000) / 16) (1960579839 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((898102913 / 250000000) : ℝ) / 16) ≤ (1961240507 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (898102913 / 250000000) / 16) (1961240507 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((171 / 2560) : ℝ) (4291 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3590614751 / 1000000000) (898102913 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (171 / 2560) (4291 / 64000) (1142928410651 / 1000000000000) (1143500017747 / 1000000000000) (3590614751 / 1000000000) (898102913 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (171 / 2560) (4291 / 64000) (3590614751 / 1000000000) (898102913 / 250000000) (834769 / 40000000000) (20982029 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3590614751 / 1000000000) (898102913 / 250000000) (1960579839 / 1000000000) (1961240507 / 1000000000) (834769 / 40000000000) (20982029 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0930 :
    ∀ t ∈ Set.Icc ((4291 / 64000) : ℝ) (4307 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((571750008873 / 500000000000) : ℝ) ≤ Real.exp (2 * (4291 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4291 / 64000)) (571750008873 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4307 / 64000) : ℝ)) ≤ (1144071910717 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4307 / 64000)) (1144071910717 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((392248017 / 200000000) : ℝ) ≤ Real.exp (3 * (3592410507 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3592410507 / 1000000000) / 16) (392248017 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3594208307 / 1000000000) : ℝ) / 16) ≤ (1961901307 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3594208307 / 1000000000) / 16) (1961901307 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4291 / 64000) : ℝ) (4307 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3592410507 / 1000000000) (3594208307 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4291 / 64000) (4307 / 64000) (571750008873 / 500000000000) (1144071910717 / 1000000000000) (3592410507 / 1000000000) (3594208307 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4291 / 64000) (4307 / 64000) (3592410507 / 1000000000) (3594208307 / 1000000000) (20757043 / 1000000000000) (10434649 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3592410507 / 1000000000) (3594208307 / 1000000000) (392248017 / 200000000) (1961901307 / 1000000000) (20757043 / 1000000000000) (10434649 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0931 :
    ∀ t ∈ Set.Icc ((4307 / 64000) : ℝ) (4323 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((286017977679 / 250000000000) : ℝ) ≤ Real.exp (2 * (4307 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4307 / 64000)) (286017977679 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4323 / 64000) : ℝ)) ≤ (228928817941 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4323 / 64000)) (228928817941 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((392380177 / 200000000) : ℝ) ≤ Real.exp (3 * (1797103581 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1797103581 / 500000000) / 16) (392380177 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((179800293 / 50000000) : ℝ) / 16) ≤ (98128133 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (179800293 / 50000000) / 16) (98128133 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4307 / 64000) : ℝ) (4323 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1797103581 / 500000000) (179800293 / 50000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4307 / 64000) (4323 / 64000) (286017977679 / 250000000000) (228928817941 / 200000000000) (1797103581 / 500000000) (179800293 / 50000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4307 / 64000) (4323 / 64000) (1797103581 / 500000000) (179800293 / 50000000) (20645409 / 1000000000000) (4151423 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1797103581 / 500000000) (179800293 / 50000000) (392380177 / 200000000) (98128133 / 50000000) (20645409 / 1000000000000) (4151423 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0932 :
    ∀ t ∈ Set.Icc ((4323 / 64000) : ℝ) (4339 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((143080511213 / 125000000000) : ℝ) ≤ Real.exp (2 * (4323 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4323 / 64000)) (143080511213 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4339 / 64000) : ℝ)) ≤ (572608277427 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4339 / 64000)) (572608277427 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((981281119 / 500000000) : ℝ) ≤ Real.exp (3 * (719200943 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (719200943 / 200000000) / 16) (981281119 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3597804313 / 1000000000) : ℝ) / 16) ≤ (245403071 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3597804313 / 1000000000) / 16) (245403071 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4323 / 64000) : ℝ) (4339 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (719200943 / 200000000) (3597804313 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4323 / 64000) (4339 / 64000) (143080511213 / 125000000000) (572608277427 / 500000000000) (719200943 / 200000000) (3597804313 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4323 / 64000) (4339 / 64000) (719200943 / 200000000) (3597804313 / 1000000000) (20534319 / 1000000000000) (20645481 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (719200943 / 200000000) (3597804313 / 1000000000) (981281119 / 500000000) (245403071 / 125000000) (20534319 / 1000000000000) (20645481 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0933 :
    ∀ t ∈ Set.Icc ((4339 / 64000) : ℝ) (871 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1145216554853 / 1000000000000) : ℝ) ≤ Real.exp (2 * (4339 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4339 / 64000)) (1145216554853 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((871 / 12800) : ℝ)) ≤ (286447326577 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (871 / 12800)) (286447326577 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((122701509 / 62500000) : ℝ) ≤ Real.exp (3 * (1798901583 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1798901583 / 500000000) / 16) (122701509 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((719920733 / 200000000) : ℝ) / 16) ≤ (1963887029 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (719920733 / 200000000) / 16) (1963887029 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4339 / 64000) : ℝ) (871 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1798901583 / 500000000) (719920733 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4339 / 64000) (871 / 12800) (1145216554853 / 1000000000000) (286447326577 / 250000000000) (1798901583 / 500000000) (719920733 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4339 / 64000) (871 / 12800) (1798901583 / 500000000) (719920733 / 200000000) (5105943 / 250000000000) (20534391 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1798901583 / 500000000) (719920733 / 200000000) (122701509 / 62500000) (1963887029 / 1000000000) (5105943 / 250000000000) (20534391 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0934 :
    ∀ t ∈ Set.Icc ((871 / 12800) : ℝ) (4371 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1145789306307 / 1000000000000) : ℝ) ≤ Real.exp (2 * (871 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (871 / 12800)) (1145789306307 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4371 / 64000) : ℝ)) ≤ (71647646513 / 62500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4371 / 64000)) (71647646513 / 62500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((981943303 / 500000000) : ℝ) ≤ Real.exp (3 * (1799801259 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1799801259 / 500000000) / 16) (981943303 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3601403917 / 1000000000) : ℝ) / 16) ≤ (982275023 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3601403917 / 1000000000) / 16) (982275023 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((871 / 12800) : ℝ) (4371 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1799801259 / 500000000) (3601403917 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (871 / 12800) (4371 / 64000) (1145789306307 / 1000000000000) (71647646513 / 62500000000) (1799801259 / 500000000) (3601403917 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (871 / 12800) (4371 / 64000) (1799801259 / 500000000) (3601403917 / 1000000000) (10156883 / 500000000000) (5105961 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1799801259 / 500000000) (3601403917 / 1000000000) (981943303 / 500000000) (982275023 / 500000000) (10156883 / 500000000000) (5105961 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0935 :
    ∀ t ∈ Set.Icc ((4371 / 64000) : ℝ) (4387 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1146362344207 / 1000000000000) : ℝ) ≤ Real.exp (2 * (4371 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4371 / 64000)) (1146362344207 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4387 / 64000) : ℝ)) ≤ (11469356687 / 10000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4387 / 64000)) (11469356687 / 10000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((982274811 / 500000000) : ℝ) ≤ Real.exp (3 * (3601402769 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3601402769 / 1000000000) / 16) (982274811 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3603205069 / 1000000000) : ℝ) / 16) ≤ (982606809 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3603205069 / 1000000000) / 16) (982606809 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4371 / 64000) : ℝ) (4387 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3601402769 / 1000000000) (3603205069 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4371 / 64000) (4387 / 64000) (1146362344207 / 1000000000000) (11469356687 / 10000000000) (3601402769 / 1000000000) (3603205069 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4371 / 64000) (4387 / 64000) (3601402769 / 1000000000) (3603205069 / 1000000000) (20204297 / 1000000000000) (20313837 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3601402769 / 1000000000) (3603205069 / 1000000000) (982274811 / 500000000) (982606809 / 500000000) (20204297 / 1000000000000) (20313837 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0936 :
    ∀ t ∈ Set.Icc ((4387 / 64000) : ℝ) (4403 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1146935668699 / 1000000000000) : ℝ) ≤ Real.exp (2 * (4387 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4387 / 64000)) (1146935668699 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4403 / 64000) : ℝ)) ≤ (45900371197 / 40000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4403 / 64000)) (45900371197 / 40000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((982606597 / 500000000) : ℝ) ≤ Real.exp (3 * (3603203921 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3603203921 / 1000000000) / 16) (982606597 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1802503561 / 500000000) : ℝ) / 16) ≤ (982938873 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1802503561 / 500000000) / 16) (982938873 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4387 / 64000) : ℝ) (4403 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3603203921 / 1000000000) (1802503561 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4387 / 64000) (4403 / 64000) (1146935668699 / 1000000000000) (45900371197 / 40000000000) (3603203921 / 1000000000) (1802503561 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4387 / 64000) (4403 / 64000) (3603203921 / 1000000000) (1802503561 / 500000000) (5023841 / 250000000000) (1262773 / 62500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3603203921 / 1000000000) (1802503561 / 500000000) (982606597 / 500000000) (982938873 / 500000000) (5023841 / 250000000000) (1262773 / 62500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0937 :
    ∀ t ∈ Set.Icc ((4403 / 64000) : ℝ) (4419 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((286877319981 / 250000000000) : ℝ) ≤ Real.exp (2 * (4403 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4403 / 64000)) (286877319981 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4419 / 64000) : ℝ)) ≤ (1148083178027 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4419 / 64000)) (1148083178027 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1965877321 / 1000000000) : ℝ) ≤ Real.exp (3 * (3605005973 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3605005973 / 1000000000) / 16) (1965877321 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((901702519 / 250000000) : ℝ) / 16) ≤ (1966542431 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (901702519 / 250000000) / 16) (1966542431 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4403 / 64000) : ℝ) (4419 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3605005973 / 1000000000) (901702519 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4403 / 64000) (4419 / 64000) (286877319981 / 250000000000) (1148083178027 / 1000000000000) (3605005973 / 1000000000) (901702519 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4403 / 64000) (4419 / 64000) (3605005973 / 1000000000) (901702519 / 250000000) (3997393 / 200000000000) (4019087 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3605005973 / 1000000000) (901702519 / 250000000) (1965877321 / 1000000000) (1966542431 / 1000000000) (3997393 / 200000000000) (4019087 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0938 :
    ∀ t ∈ Set.Icc ((4419 / 64000) : ℝ) (887 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((574041589013 / 500000000000) : ℝ) ≤ Real.exp (2 * (4419 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4419 / 64000)) (574041589013 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((887 / 12800) : ℝ)) ≤ (1148657363151 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (887 / 12800)) (1148657363151 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((983271003 / 500000000) : ℝ) ≤ Real.exp (3 * (3606808927 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3606808927 / 1000000000) / 16) (983271003 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((902153483 / 250000000) : ℝ) / 16) ≤ (1967207673 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (902153483 / 250000000) / 16) (1967207673 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4419 / 64000) : ℝ) (887 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3606808927 / 1000000000) (902153483 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4419 / 64000) (887 / 12800) (574041589013 / 500000000000) (1148657363151 / 1000000000000) (3606808927 / 1000000000) (902153483 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4419 / 64000) (887 / 12800) (3606808927 / 1000000000) (902153483 / 250000000) (2484887 / 125000000000) (3997407 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3606808927 / 1000000000) (902153483 / 250000000) (983271003 / 500000000) (1967207673 / 1000000000) (2484887 / 125000000000) (3997407 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0939 :
    ∀ t ∈ Set.Icc ((887 / 12800) : ℝ) (4451 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((22973147263 / 20000000000) : ℝ) ≤ Real.exp (2 * (887 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (887 / 12800)) (22973147263 / 20000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4451 / 64000) : ℝ)) ≤ (1149231835439 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4451 / 64000)) (1149231835439 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((122950453 / 62500000) : ℝ) ≤ Real.exp (3 * (1804306391 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1804306391 / 500000000) / 16) (122950453 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((361041869 / 100000000) : ℝ) / 16) ≤ (1967873473 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (361041869 / 100000000) / 16) (1967873473 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((887 / 12800) : ℝ) (4451 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1804306391 / 500000000) (361041869 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (887 / 12800) (4451 / 64000) (22973147263 / 20000000000) (1149231835439 / 1000000000000) (1804306391 / 500000000) (361041869 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (887 / 12800) (4451 / 64000) (1804306391 / 500000000) (361041869 / 100000000) (4942939 / 250000000000) (9939583 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1804306391 / 500000000) (361041869 / 100000000) (122950453 / 62500000) (1967873473 / 1000000000) (4942939 / 250000000000) (9939583 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch046 :
    ∀ t ∈ Set.Icc ((4131 / 64000) : ℝ) (4451 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0920
      hpThetaDensityTwoTermCompact_cell0921)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0922
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0923
      hpThetaDensityTwoTermCompact_cell0924)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0925
      hpThetaDensityTwoTermCompact_cell0926)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0927
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0928
      hpThetaDensityTwoTermCompact_cell0929))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0930
      hpThetaDensityTwoTermCompact_cell0931)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0932
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0933
      hpThetaDensityTwoTermCompact_cell0934)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0935
      hpThetaDensityTwoTermCompact_cell0936)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0937
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0938
      hpThetaDensityTwoTermCompact_cell0939)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch046
end HodgeProofHP
