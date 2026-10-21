/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0700 :
    ∀ t ∈ Set.Icc ((2383 / 64000) : ℝ) (2387 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((538655838503 / 500000000000) : ℝ) ≤ Real.exp (2 * (2383 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2383 / 64000)) (538655838503 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2387 / 64000) : ℝ)) ≤ (1077446349383 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2387 / 64000)) (1077446349383 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((235780801 / 125000000) : ℝ) ≤ Real.exp (3 * (676894749 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (676894749 / 200000000) / 16) (235780801 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((338489791 / 100000000) : ℝ) / 16) ≤ (188639643 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (338489791 / 100000000) / 16) (188639643 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2383 / 64000) : ℝ) (2387 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (676894749 / 200000000) (338489791 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2383 / 64000) (2387 / 64000) (538655838503 / 500000000000) (1077446349383 / 1000000000000) (676894749 / 200000000) (338489791 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2383 / 64000) (2387 / 64000) (676894749 / 200000000) (338489791 / 100000000) (19446549 / 500000000000) (19471311 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (676894749 / 200000000) (338489791 / 100000000) (235780801 / 125000000) (188639643 / 100000000) (19446549 / 500000000000) (19471311 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0701 :
    ∀ t ∈ Set.Icc ((2387 / 64000) : ℝ) (2391 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((538723174691 / 500000000000) : ℝ) ≤ Real.exp (2 * (2387 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2387 / 64000)) (538723174691 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2391 / 64000) : ℝ)) ≤ (215516207719 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2391 / 64000)) (215516207719 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((117899753 / 62500000) : ℝ) ≤ Real.exp (3 * (3384896831 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3384896831 / 1000000000) / 16) (117899753 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((423165131 / 125000000) : ℝ) / 16) ≤ (18865461 / 10000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (423165131 / 125000000) / 16) (18865461 / 10000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2387 / 64000) : ℝ) (2391 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3384896831 / 1000000000) (423165131 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2387 / 64000) (2391 / 64000) (538723174691 / 500000000000) (215516207719 / 200000000000) (3384896831 / 1000000000) (423165131 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2387 / 64000) (2391 / 64000) (3384896831 / 1000000000) (423165131 / 125000000) (19421879 / 500000000000) (1555729 / 40000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3384896831 / 1000000000) (423165131 / 125000000) (117899753 / 62500000) (18865461 / 10000000) (19421879 / 500000000000) (1555729 / 40000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0702 :
    ∀ t ∈ Set.Icc ((2391 / 64000) : ℝ) (479 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((538790519297 / 500000000000) : ℝ) ≤ Real.exp (2 * (2391 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2391 / 64000)) (538790519297 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((479 / 12800) : ℝ)) ≤ (269428936161 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (479 / 12800)) (269428936161 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1886545717 / 1000000000) : ℝ) ≤ Real.exp (3 * (338531997 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (338531997 / 100000000) / 16) (1886545717 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((42321803 / 12500000) : ℝ) / 16) ≤ (9433479 / 5000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (42321803 / 12500000) / 16) (9433479 / 5000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2391 / 64000) : ℝ) (479 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (338531997 / 100000000) (42321803 / 12500000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2391 / 64000) (479 / 12800) (538790519297 / 500000000000) (269428936161 / 250000000000) (338531997 / 100000000) (42321803 / 12500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2391 / 64000) (479 / 12800) (338531997 / 100000000) (42321803 / 12500000) (19397237 / 500000000000) (7768777 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (338531997 / 100000000) (42321803 / 12500000) (1886545717 / 1000000000) (9433479 / 5000000) (19397237 / 500000000000) (7768777 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0703 :
    ∀ t ∈ Set.Icc ((479 / 12800) : ℝ) (2399 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1077715744643 / 1000000000000) : ℝ) ≤ Real.exp (2 * (479 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (479 / 12800)) (1077715744643 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2399 / 64000) : ℝ)) ≤ (269462616883 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2399 / 64000)) (269462616883 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((943347709 / 500000000) : ℝ) ≤ Real.exp (3 * (3385743161 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3385743161 / 1000000000) / 16) (943347709 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((846541871 / 250000000) : ℝ) / 16) ≤ (1886845531 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (846541871 / 250000000) / 16) (1886845531 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((479 / 12800) : ℝ) (2399 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3385743161 / 1000000000) (846541871 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (479 / 12800) (2399 / 64000) (1077715744643 / 1000000000000) (269462616883 / 250000000000) (3385743161 / 1000000000) (846541871 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (479 / 12800) (2399 / 64000) (3385743161 / 1000000000) (846541871 / 250000000) (38745247 / 1000000000000) (38794601 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3385743161 / 1000000000) (846541871 / 250000000) (943347709 / 500000000) (1886845531 / 1000000000) (38745247 / 1000000000000) (38794601 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0704 :
    ∀ t ∈ Set.Icc ((2399 / 64000) : ℝ) (2403 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1077850467531 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2399 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2399 / 64000)) (1077850467531 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2403 / 64000) : ℝ)) ≤ (1077985207261 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2403 / 64000)) (1077985207261 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((471711287 / 250000000) : ℝ) ≤ Real.exp (3 * (677233281 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (677233281 / 200000000) / 16) (471711287 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1693295391 / 500000000) : ℝ) / 16) ≤ (1886995293 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1693295391 / 500000000) / 16) (1886995293 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2399 / 64000) : ℝ) (2403 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (677233281 / 200000000) (1693295391 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2399 / 64000) (2403 / 64000) (1077850467531 / 1000000000000) (1077985207261 / 1000000000000) (677233281 / 200000000) (1693295391 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2399 / 64000) (2403 / 64000) (677233281 / 200000000) (1693295391 / 500000000) (9674019 / 250000000000) (19372687 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (677233281 / 200000000) (1693295391 / 500000000) (471711287 / 250000000) (1886995293 / 1000000000) (9674019 / 250000000000) (19372687 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0705 :
    ∀ t ∈ Set.Icc ((2403 / 64000) : ℝ) (2407 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((53899260363 / 50000000000) : ℝ) ≤ Real.exp (2 * (2403 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2403 / 64000)) (53899260363 / 50000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2407 / 64000) : ℝ)) ≤ (539059981917 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2407 / 64000)) (539059981917 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((188699491 / 100000000) : ℝ) ≤ Real.exp (3 * (3386589703 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3386589703 / 1000000000) / 16) (188699491 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((846753533 / 250000000) : ℝ) / 16) ≤ (377429017 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (846753533 / 250000000) / 16) (377429017 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2403 / 64000) : ℝ) (2407 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3386589703 / 1000000000) (846753533 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2403 / 64000) (2407 / 64000) (53899260363 / 50000000000) (539059981917 / 500000000000) (3386589703 / 1000000000) (846753533 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2403 / 64000) (2407 / 64000) (3386589703 / 1000000000) (846753533 / 250000000) (38646961 / 1000000000000) (19348101 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3386589703 / 1000000000) (846753533 / 250000000) (188699491 / 100000000) (377429017 / 200000000) (38646961 / 1000000000000) (19348101 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0706 :
    ∀ t ∈ Set.Icc ((2407 / 64000) : ℝ) (2411 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1078119963833 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2407 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2407 / 64000)) (1078119963833 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2411 / 64000) : ℝ)) ≤ (1078254737253 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2411 / 64000)) (1078254737253 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((943572351 / 500000000) : ℝ) ≤ Real.exp (3 * (3387013053 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3387013053 / 1000000000) / 16) (943572351 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((677487507 / 200000000) : ℝ) / 16) ≤ (471823727 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (677487507 / 200000000) / 16) (471823727 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2407 / 64000) : ℝ) (2411 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3387013053 / 1000000000) (677487507 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2407 / 64000) (2411 / 64000) (1078119963833 / 1000000000000) (1078254737253 / 1000000000000) (3387013053 / 1000000000) (677487507 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2407 / 64000) (2411 / 64000) (3387013053 / 1000000000) (677487507 / 200000000) (19298951 / 500000000000) (2415443 / 62500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3387013053 / 1000000000) (677487507 / 200000000) (943572351 / 500000000) (471823727 / 250000000) (19298951 / 500000000000) (2415443 / 62500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0707 :
    ∀ t ∈ Set.Icc ((2411 / 64000) : ℝ) (483 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((269563684313 / 250000000000) : ℝ) ≤ Real.exp (2 * (2411 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2411 / 64000)) (269563684313 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((483 / 12800) : ℝ)) ≤ (1078389527519 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (483 / 12800)) (1078389527519 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((75491781 / 40000000) : ℝ) ≤ Real.exp (3 * (423429557 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (423429557 / 125000000) / 16) (75491781 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3387860991 / 1000000000) : ℝ) / 16) ≤ (1887444761 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3387860991 / 1000000000) / 16) (1887444761 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2411 / 64000) : ℝ) (483 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (423429557 / 125000000) (3387860991 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2411 / 64000) (483 / 12800) (269563684313 / 250000000000) (1078389527519 / 1000000000000) (423429557 / 125000000) (3387860991 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2411 / 64000) (483 / 12800) (423429557 / 125000000) (3387860991 / 1000000000) (385489 / 10000000000) (38598029 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (423429557 / 125000000) (3387860991 / 1000000000) (75491781 / 40000000) (1887444761 / 1000000000) (385489 / 10000000000) (38598029 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0708 :
    ∀ t ∈ Set.Icc ((483 / 12800) : ℝ) (2419 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((539194763759 / 500000000000) : ℝ) ≤ Real.exp (2 * (483 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (483 / 12800)) (539194763759 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2419 / 64000) : ℝ)) ≤ (215704866927 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2419 / 64000)) (215704866927 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((943722189 / 500000000) : ℝ) ≤ Real.exp (3 * (423482489 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (423482489 / 125000000) / 16) (943722189 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3388284501 / 1000000000) : ℝ) / 16) ≤ (943797323 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3388284501 / 1000000000) / 16) (943797323 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((483 / 12800) : ℝ) (2419 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (423482489 / 125000000) (3388284501 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (483 / 12800) (2419 / 64000) (539194763759 / 500000000000) (215704866927 / 200000000000) (423482489 / 125000000) (3388284501 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (483 / 12800) (2419 / 64000) (423482489 / 125000000) (3388284501 / 1000000000) (19249977 / 500000000000) (19274513 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (423482489 / 125000000) (3388284501 / 1000000000) (943722189 / 500000000) (943797323 / 500000000) (19249977 / 500000000000) (19274513 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0709 :
    ∀ t ∈ Set.Icc ((2419 / 64000) : ℝ) (2423 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((539262167317 / 500000000000) : ℝ) ≤ Real.exp (2 * (2419 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2419 / 64000)) (539262167317 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2423 / 64000) : ℝ)) ≤ (269664789651 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2423 / 64000)) (269664789651 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((943797131 / 500000000) : ℝ) ≤ Real.exp (3 * (3388283421 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3388283421 / 1000000000) / 16) (943797131 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3388708063 / 1000000000) : ℝ) / 16) ≤ (23596807 / 12500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3388708063 / 1000000000) / 16) (23596807 / 12500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2419 / 64000) : ℝ) (2423 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3388283421 / 1000000000) (3388708063 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2419 / 64000) (2423 / 64000) (539262167317 / 500000000000) (269664789651 / 250000000000) (3388283421 / 1000000000) (3388708063 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2419 / 64000) (2423 / 64000) (3388283421 / 1000000000) (3388708063 / 1000000000) (38451063 / 1000000000000) (481251 / 12500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3388283421 / 1000000000) (3388708063 / 1000000000) (943797131 / 500000000) (23596807 / 12500000) (38451063 / 1000000000000) (481251 / 12500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0710 :
    ∀ t ∈ Set.Icc ((2423 / 64000) : ℝ) (2427 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1078659158603 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2423 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2423 / 64000)) (1078659158603 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2427 / 64000) : ℝ)) ≤ (539396999713 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2427 / 64000)) (539396999713 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1887744177 / 1000000000) : ℝ) ≤ Real.exp (3 * (3388706983 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3388706983 / 1000000000) / 16) (1887744177 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1694565839 / 500000000) : ℝ) / 16) ≤ (943947253 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1694565839 / 500000000) / 16) (943947253 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2423 / 64000) : ℝ) (2427 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3388706983 / 1000000000) (1694565839 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2423 / 64000) (2427 / 64000) (1078659158603 / 1000000000000) (539396999713 / 500000000000) (3388706983 / 1000000000) (1694565839 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2423 / 64000) (2427 / 64000) (3388706983 / 1000000000) (1694565839 / 500000000) (38402229 / 1000000000000) (38451189 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3388706983 / 1000000000) (1694565839 / 500000000) (1887744177 / 1000000000) (943947253 / 500000000) (38402229 / 1000000000000) (38451189 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0711 :
    ∀ t ∈ Set.Icc ((2427 / 64000) : ℝ) (2431 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((43151759977 / 40000000000) : ℝ) ≤ Real.exp (2 * (2427 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2427 / 64000)) (43151759977 / 40000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2431 / 64000) : ℝ)) ≤ (67433053569 / 62500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2431 / 64000)) (67433053569 / 62500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((943947061 / 500000000) : ℝ) ≤ Real.exp (3 * (1694565299 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1694565299 / 500000000) / 16) (943947061 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((677911069 / 200000000) : ℝ) / 16) ≤ (1888044481 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (677911069 / 200000000) / 16) (1888044481 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2427 / 64000) : ℝ) (2431 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1694565299 / 500000000) (677911069 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2427 / 64000) (2431 / 64000) (43151759977 / 40000000000) (67433053569 / 62500000000) (1694565299 / 500000000) (677911069 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2427 / 64000) (2431 / 64000) (1694565299 / 500000000) (677911069 / 200000000) (38353451 / 1000000000000) (7680471 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1694565299 / 500000000) (677911069 / 200000000) (943947061 / 500000000) (1888044481 / 1000000000) (38353451 / 1000000000000) (7680471 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0712 :
    ∀ t ∈ Set.Icc ((2431 / 64000) : ℝ) (487 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1078928857103 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2431 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2431 / 64000)) (1078928857103 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((487 / 12800) : ℝ)) ≤ (1079063731641 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (487 / 12800)) (1079063731641 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((944022049 / 500000000) : ℝ) ≤ Real.exp (3 * (1694777133 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1694777133 / 500000000) / 16) (944022049 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1694989533 / 500000000) : ℝ) / 16) ≤ (236024311 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1694989533 / 500000000) / 16) (236024311 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2431 / 64000) : ℝ) (487 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1694777133 / 500000000) (1694989533 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2431 / 64000) (487 / 12800) (1078928857103 / 1000000000000) (1079063731641 / 1000000000000) (1694777133 / 500000000) (1694989533 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2431 / 64000) (487 / 12800) (1694777133 / 500000000) (1694989533 / 500000000) (4788091 / 125000000000) (4794197 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1694777133 / 500000000) (1694989533 / 500000000) (944022049 / 500000000) (236024311 / 125000000) (4788091 / 125000000000) (4794197 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0713 :
    ∀ t ∈ Set.Icc ((487 / 12800) : ℝ) (2439 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((26976593291 / 25000000000) : ℝ) ≤ Real.exp (2 * (487 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (487 / 12800)) (26976593291 / 25000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2439 / 64000) : ℝ)) ≤ (539599311519 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2439 / 64000)) (539599311519 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((377638821 / 200000000) : ℝ) ≤ Real.exp (3 * (1694988993 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1694988993 / 500000000) / 16) (377638821 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((84760071 / 25000000) : ℝ) / 16) ≤ (75533781 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (84760071 / 25000000) / 16) (75533781 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((487 / 12800) : ℝ) (2439 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1694988993 / 500000000) (84760071 / 25000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (487 / 12800) (2439 / 64000) (26976593291 / 25000000000) (539599311519 / 500000000000) (1694988993 / 500000000) (84760071 / 25000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (487 / 12800) (2439 / 64000) (1694988993 / 500000000) (84760071 / 25000000) (19128031 / 500000000000) (19152427 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1694988993 / 500000000) (84760071 / 25000000) (377638821 / 200000000) (75533781 / 40000000) (19128031 / 500000000000) (19152427 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0714 :
    ∀ t ∈ Set.Icc ((2439 / 64000) : ℝ) (2443 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1079198623037 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2439 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2439 / 64000)) (1079198623037 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2443 / 64000) : ℝ)) ≤ (1079333531297 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2443 / 64000)) (1079333531297 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((944172071 / 500000000) : ℝ) ≤ Real.exp (3 * (21190011 / 6250000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (21190011 / 6250000) / 16) (944172071 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3390826667 / 1000000000) : ℝ) / 16) ≤ (944247297 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3390826667 / 1000000000) / 16) (944247297 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2439 / 64000) : ℝ) (2443 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (21190011 / 6250000) (3390826667 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2439 / 64000) (2443 / 64000) (1079198623037 / 1000000000000) (1079333531297 / 1000000000000) (21190011 / 6250000) (3390826667 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2439 / 64000) (2443 / 64000) (21190011 / 6250000) (3390826667 / 1000000000) (764149 / 20000000000) (38256187 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (21190011 / 6250000) (3390826667 / 1000000000) (944172071 / 500000000) (944247297 / 500000000) (764149 / 20000000000) (38256187 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0715 :
    ∀ t ∈ Set.Icc ((2443 / 64000) : ℝ) (2447 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((33729172853 / 31250000000) : ℝ) ≤ Real.exp (2 * (2443 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2443 / 64000)) (33729172853 / 31250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2447 / 64000) : ℝ)) ≤ (1079468456421 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2447 / 64000)) (1079468456421 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((188849421 / 100000000) : ℝ) ≤ Real.exp (3 * (3390825587 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3390825587 / 1000000000) / 16) (188849421 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3391250547 / 1000000000) : ℝ) / 16) ≤ (472161173 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3391250547 / 1000000000) / 16) (472161173 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2443 / 64000) : ℝ) (2447 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3390825587 / 1000000000) (3391250547 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2443 / 64000) (2447 / 64000) (33729172853 / 31250000000) (1079468456421 / 1000000000000) (3390825587 / 1000000000) (3391250547 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2443 / 64000) (2447 / 64000) (3390825587 / 1000000000) (3391250547 / 1000000000) (2384931 / 62500000000) (4775947 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3390825587 / 1000000000) (3391250547 / 1000000000) (188849421 / 100000000) (472161173 / 250000000) (2384931 / 62500000000) (4775947 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0716 :
    ∀ t ∈ Set.Icc ((2447 / 64000) : ℝ) (2451 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((53973422821 / 50000000000) : ℝ) ≤ Real.exp (2 * (2447 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2447 / 64000)) (53973422821 / 50000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2451 / 64000) : ℝ)) ≤ (269900849603 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2451 / 64000)) (269900849603 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1888644309 / 1000000000) : ℝ) ≤ Real.exp (3 * (1695624733 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1695624733 / 500000000) / 16) (1888644309 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((42395931 / 12500000) : ℝ) / 16) ≤ (944397411 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (42395931 / 12500000) / 16) (944397411 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2447 / 64000) : ℝ) (2451 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1695624733 / 500000000) (42395931 / 12500000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2447 / 64000) (2451 / 64000) (53973422821 / 50000000000) (269900849603 / 250000000000) (1695624733 / 500000000) (42395931 / 12500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2447 / 64000) (2451 / 64000) (1695624733 / 500000000) (42395931 / 12500000) (9527599 / 250000000000) (1907951 / 50000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1695624733 / 500000000) (42395931 / 12500000) (1888644309 / 1000000000) (944397411 / 500000000) (9527599 / 250000000000) (1907951 / 50000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0717 :
    ∀ t ∈ Set.Icc ((2451 / 64000) : ℝ) (491 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1079603398411 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2451 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2451 / 64000)) (1079603398411 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((491 / 12800) : ℝ)) ≤ (134967294659 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (491 / 12800)) (134967294659 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((944397219 / 500000000) : ℝ) ≤ Real.exp (3 * (3391673399 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3391673399 / 1000000000) / 16) (944397219 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1696049233 / 500000000) : ℝ) / 16) ≤ (944472491 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1696049233 / 500000000) / 16) (944472491 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2451 / 64000) : ℝ) (491 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3391673399 / 1000000000) (1696049233 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2451 / 64000) (491 / 12800) (1079603398411 / 1000000000000) (134967294659 / 125000000000) (3391673399 / 1000000000) (1696049233 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2451 / 64000) (491 / 12800) (3391673399 / 1000000000) (1696049233 / 500000000) (297359 / 7812500000) (38110521 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3391673399 / 1000000000) (1696049233 / 500000000) (944397219 / 500000000) (944472491 / 500000000) (297359 / 7812500000) (38110521 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0718 :
    ∀ t ∈ Set.Icc ((491 / 12800) : ℝ) (2459 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1079738357271 / 1000000000000) : ℝ) ≤ Real.exp (2 * (491 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (491 / 12800)) (1079738357271 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2459 / 64000) : ℝ)) ≤ (539936666501 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2459 / 64000)) (539936666501 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((944472299 / 500000000) : ℝ) ≤ Real.exp (3 * (678419477 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (678419477 / 200000000) / 16) (944472299 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((424065313 / 125000000) : ℝ) / 16) ≤ (1889095173 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (424065313 / 125000000) / 16) (1889095173 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((491 / 12800) : ℝ) (2459 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (678419477 / 200000000) (424065313 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (491 / 12800) (2459 / 64000) (1079738357271 / 1000000000000) (539936666501 / 500000000000) (678419477 / 200000000) (424065313 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (491 / 12800) (2459 / 64000) (678419477 / 200000000) (424065313 / 125000000) (38013563 / 1000000000000) (38062077 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (678419477 / 200000000) (424065313 / 125000000) (944472299 / 500000000) (1889095173 / 1000000000) (38013563 / 1000000000000) (38062077 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0719 :
    ∀ t ∈ Set.Icc ((2459 / 64000) : ℝ) (2463 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1079873333001 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2459 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2459 / 64000)) (1079873333001 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2463 / 64000) : ℝ)) ≤ (540004162803 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2463 / 64000)) (540004162803 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1889094789 / 1000000000) : ℝ) ≤ Real.exp (3 * (3392521423 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3392521423 / 1000000000) / 16) (1889094789 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((848236649 / 250000000) : ℝ) / 16) ≤ (944622697 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (848236649 / 250000000) / 16) (944622697 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2459 / 64000) : ℝ) (2463 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3392521423 / 1000000000) (848236649 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2459 / 64000) (2463 / 64000) (1079873333001 / 1000000000000) (540004162803 / 500000000000) (3392521423 / 1000000000) (848236649 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2459 / 64000) (2463 / 64000) (3392521423 / 1000000000) (848236649 / 250000000) (37965231 / 1000000000000) (4751711 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3392521423 / 1000000000) (848236649 / 250000000) (1889094789 / 1000000000) (944622697 / 500000000) (37965231 / 1000000000000) (4751711 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch035 :
    ∀ t ∈ Set.Icc ((2383 / 64000) : ℝ) (2463 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0700
      hpThetaDensityTwoTermCompact_cell0701)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0702
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0703
      hpThetaDensityTwoTermCompact_cell0704)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0705
      hpThetaDensityTwoTermCompact_cell0706)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0707
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0708
      hpThetaDensityTwoTermCompact_cell0709))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0710
      hpThetaDensityTwoTermCompact_cell0711)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0712
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0713
      hpThetaDensityTwoTermCompact_cell0714)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0715
      hpThetaDensityTwoTermCompact_cell0716)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0717
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0718
      hpThetaDensityTwoTermCompact_cell0719)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch035
end HodgeProofHP
