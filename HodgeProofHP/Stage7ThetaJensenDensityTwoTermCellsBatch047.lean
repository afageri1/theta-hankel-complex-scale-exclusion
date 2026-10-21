/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0940 :
    ∀ t ∈ Set.Icc ((4451 / 64000) : ℝ) (4467 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((574615917719 / 500000000000) : ℝ) ≤ Real.exp (2 * (4451 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4451 / 64000)) (574615917719 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4467 / 64000) : ℝ)) ≤ (574903297517 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4467 / 64000)) (574903297517 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((245984131 / 125000000) : ℝ) ≤ Real.exp (3 * (180520877 / 50000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (180520877 / 50000000) / 16) (245984131 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3612224351 / 1000000000) : ℝ) / 16) ≤ (246067479 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3612224351 / 1000000000) / 16) (246067479 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4451 / 64000) : ℝ) (4467 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (180520877 / 50000000) (3612224351 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4451 / 64000) (4467 / 64000) (574615917719 / 500000000000) (574903297517 / 500000000000) (180520877 / 50000000) (3612224351 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4451 / 64000) (4467 / 64000) (180520877 / 50000000) (3612224351 / 1000000000) (9832471 / 500000000000) (790873 / 40000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (180520877 / 50000000) (3612224351 / 1000000000) (245984131 / 125000000) (246067479 / 125000000) (9832471 / 500000000000) (790873 / 40000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0941 :
    ∀ t ∈ Set.Icc ((4467 / 64000) : ℝ) (4483 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1149806595033 / 1000000000000) : ℝ) ≤ Real.exp (2 * (4467 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4467 / 64000)) (1149806595033 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4483 / 64000) : ℝ)) ≤ (1150381642081 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4483 / 64000)) (1150381642081 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((984269703 / 500000000) : ℝ) ≤ Real.exp (3 * (4515279 / 1250000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4515279 / 1250000) / 16) (984269703 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((722806183 / 200000000) : ℝ) / 16) ≤ (7876827 / 4000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (722806183 / 200000000) / 16) (7876827 / 4000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4467 / 64000) : ℝ) (4483 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4515279 / 1250000) (722806183 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4467 / 64000) (4483 / 64000) (1149806595033 / 1000000000000) (1150381642081 / 1000000000000) (4515279 / 1250000) (722806183 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4467 / 64000) (4483 / 64000) (4515279 / 1250000) (722806183 / 200000000) (19558653 / 1000000000000) (4916253 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (4515279 / 1250000) (722806183 / 200000000) (984269703 / 500000000) (7876827 / 4000000) (19558653 / 1000000000000) (4916253 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0942 :
    ∀ t ∈ Set.Icc ((4483 / 64000) : ℝ) (4499 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((7189885263 / 6250000000) : ℝ) ≤ Real.exp (2 * (4483 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4483 / 64000)) (7189885263 / 6250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4499 / 64000) : ℝ)) ≤ (287739244181 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4499 / 64000)) (287739244181 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((492301581 / 250000000) : ℝ) ≤ Real.exp (3 * (3614029763 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3614029763 / 1000000000) / 16) (492301581 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1807919191 / 500000000) : ℝ) / 16) ≤ (492468557 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1807919191 / 500000000) / 16) (492468557 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4483 / 64000) : ℝ) (4499 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3614029763 / 1000000000) (1807919191 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4483 / 64000) (4499 / 64000) (7189885263 / 6250000000) (287739244181 / 250000000000) (3614029763 / 1000000000) (1807919191 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4483 / 64000) (4499 / 64000) (3614029763 / 1000000000) (1807919191 / 500000000) (3890577 / 200000000000) (19558721 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3614029763 / 1000000000) (1807919191 / 500000000) (492301581 / 250000000) (492468557 / 250000000) (3890577 / 200000000000) (19558721 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0943 :
    ∀ t ∈ Set.Icc ((4499 / 64000) : ℝ) (903 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1150956976723 / 1000000000000) : ℝ) ≤ Real.exp (2 * (4499 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4499 / 64000)) (1150956976723 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((903 / 12800) : ℝ)) ≤ (575766299553 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (903 / 12800)) (575766299553 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1969873801 / 1000000000) : ℝ) ≤ Real.exp (3 * (361583723 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (361583723 / 100000000) / 16) (1969873801 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3617646753 / 1000000000) : ℝ) / 16) ≤ (394108453 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3617646753 / 1000000000) / 16) (394108453 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4499 / 64000) : ℝ) (903 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (361583723 / 100000000) (3617646753 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4499 / 64000) (903 / 12800) (1150956976723 / 1000000000000) (575766299553 / 500000000000) (361583723 / 100000000) (3617646753 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4499 / 64000) (903 / 12800) (361583723 / 100000000) (3617646753 / 1000000000) (19347637 / 1000000000000) (19452953 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (361583723 / 100000000) (3617646753 / 1000000000) (1969873801 / 1000000000) (394108453 / 200000000) (19347637 / 1000000000000) (19452953 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0944 :
    ∀ t ∈ Set.Icc ((903 / 12800) : ℝ) (4531 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((230306519821 / 200000000000) : ℝ) ≤ Real.exp (2 * (903 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (903 / 12800)) (230306519821 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4531 / 64000) : ℝ)) ≤ (1152108509371 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4531 / 64000)) (1152108509371 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1970541839 / 1000000000) : ℝ) ≤ Real.exp (3 * (3617645601 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3617645601 / 1000000000) / 16) (1970541839 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3619456029 / 1000000000) : ℝ) / 16) ≤ (123200679 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3619456029 / 1000000000) / 16) (123200679 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((903 / 12800) : ℝ) (4531 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3617645601 / 1000000000) (3619456029 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (903 / 12800) (4531 / 64000) (230306519821 / 200000000000) (1152108509371 / 1000000000000) (3617645601 / 1000000000) (3619456029 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (903 / 12800) (4531 / 64000) (3617645601 / 1000000000) (3619456029 / 1000000000) (3848581 / 200000000000) (3869541 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3617645601 / 1000000000) (3619456029 / 1000000000) (1970541839 / 1000000000) (123200679 / 62500000) (3848581 / 200000000000) (3869541 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0945 :
    ∀ t ∈ Set.Icc ((4531 / 64000) : ℝ) (4547 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((115210850937 / 100000000000) : ℝ) ≤ Real.exp (2 * (4531 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4531 / 64000)) (115210850937 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4547 / 64000) : ℝ)) ≤ (1152684707663 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4547 / 64000)) (1152684707663 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1971210437 / 1000000000) : ℝ) ≤ Real.exp (3 * (904863719 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (904863719 / 250000000) / 16) (1971210437 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3621266209 / 1000000000) : ℝ) / 16) ≤ (246485003 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3621266209 / 1000000000) / 16) (246485003 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4531 / 64000) : ℝ) (4547 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (904863719 / 250000000) (3621266209 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4531 / 64000) (4547 / 64000) (115210850937 / 100000000000) (1152684707663 / 1000000000000) (904863719 / 250000000) (3621266209 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4531 / 64000) (4547 / 64000) (904863719 / 250000000) (3621266209 / 1000000000) (19138689 / 1000000000000) (19242973 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (904863719 / 250000000) (3621266209 / 1000000000) (1971210437 / 1000000000) (246485003 / 125000000) (19138689 / 1000000000000) (19242973 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0946 :
    ∀ t ∈ Set.Icc ((4547 / 64000) : ℝ) (4563 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((576342353831 / 500000000000) : ℝ) ≤ Real.exp (2 * (4547 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4547 / 64000)) (576342353831 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4563 / 64000) : ℝ)) ≤ (1153261194127 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4563 / 64000)) (1153261194127 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((492969899 / 250000000) : ℝ) ≤ Real.exp (3 * (113164533 / 31250000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (113164533 / 31250000) / 16) (492969899 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((724615459 / 200000000) : ℝ) / 16) ≤ (986274873 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (724615459 / 200000000) / 16) (986274873 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4547 / 64000) : ℝ) (4563 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (113164533 / 31250000) (724615459 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4547 / 64000) (4563 / 64000) (576342353831 / 500000000000) (1153261194127 / 1000000000000) (113164533 / 31250000) (724615459 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4547 / 64000) (4563 / 64000) (113164533 / 31250000) (724615459 / 200000000) (9517493 / 500000000000) (19138757 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (113164533 / 31250000) (724615459 / 200000000) (492969899 / 250000000) (986274873 / 500000000) (9517493 / 500000000000) (19138757 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0947 :
    ∀ t ∈ Set.Icc ((4563 / 64000) : ℝ) (919 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((576630597063 / 500000000000) : ℝ) ≤ Real.exp (2 * (4563 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4563 / 64000)) (576630597063 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((919 / 12800) : ℝ)) ≤ (72150939509 / 62500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (919 / 12800)) (72150939509 / 62500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((986274659 / 500000000) : ℝ) ≤ Real.exp (3 * (3623076141 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3623076141 / 1000000000) / 16) (986274659 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((725340437 / 200000000) : ℝ) / 16) ≤ (986945439 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (725340437 / 200000000) / 16) (986945439 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4563 / 64000) : ℝ) (919 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3623076141 / 1000000000) (725340437 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4563 / 64000) (919 / 12800) (576630597063 / 500000000000) (72150939509 / 62500000000) (3623076141 / 1000000000) (725340437 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4563 / 64000) (919 / 12800) (3623076141 / 1000000000) (725340437 / 200000000) (4707277 / 250000000000) (19035053 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3623076141 / 1000000000) (725340437 / 200000000) (986274659 / 500000000) (986945439 / 500000000) (4707277 / 250000000000) (19035053 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0948 :
    ∀ t ∈ Set.Icc ((919 / 12800) : ℝ) (4627 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1154415032143 / 1000000000000) : ℝ) ≤ Real.exp (2 * (919 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (919 / 12800)) (1154415032143 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4627 / 64000) : ℝ)) ≤ (9027890817 / 7812500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4627 / 64000)) (9027890817 / 7812500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1973890449 / 1000000000) : ℝ) ≤ Real.exp (3 * (3626701029 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3626701029 / 1000000000) / 16) (1973890449 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3630330701 / 1000000000) : ℝ) / 16) ≤ (395046853 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3630330701 / 1000000000) / 16) (395046853 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((919 / 12800) : ℝ) (4627 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3626701029 / 1000000000) (3630330701 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (919 / 12800) (4627 / 64000) (1154415032143 / 1000000000000) (9027890817 / 7812500000) (3626701029 / 1000000000) (3630330701 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (919 / 12800) (4627 / 64000) (3626701029 / 1000000000) (3630330701 / 1000000000) (9312627 / 500000000000) (753167 / 40000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3626701029 / 1000000000) (3630330701 / 1000000000) (1973890449 / 1000000000) (395046853 / 200000000) (9312627 / 500000000000) (753167 / 40000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0949 :
    ∀ t ∈ Set.Icc ((4627 / 64000) : ℝ) (4659 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((46222800983 / 40000000000) : ℝ) ≤ Real.exp (2 * (4627 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4627 / 64000)) (46222800983 / 40000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4659 / 64000) : ℝ)) ≤ (578363086289 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4659 / 64000)) (578363086289 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((493808459 / 250000000) : ℝ) ≤ Real.exp (3 * (453791193 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (453791193 / 125000000) / 16) (493808459 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3633962847 / 1000000000) : ℝ) / 16) ≤ (247072489 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3633962847 / 1000000000) / 16) (247072489 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4627 / 64000) : ℝ) (4659 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (453791193 / 125000000) (3633962847 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4627 / 64000) (4659 / 64000) (46222800983 / 40000000000) (578363086289 / 500000000000) (453791193 / 125000000) (3633962847 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4627 / 64000) (4659 / 64000) (453791193 / 125000000) (3633962847 / 1000000000) (18423407 / 1000000000000) (465633 / 25000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (453791193 / 125000000) (3633962847 / 1000000000) (493808459 / 250000000) (247072489 / 125000000) (18423407 / 1000000000000) (465633 / 25000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0950 :
    ∀ t ∈ Set.Icc ((4659 / 64000) : ℝ) (4691 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1156726172577 / 1000000000000) : ℝ) ≤ Real.exp (2 * (4659 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4659 / 64000)) (1156726172577 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4691 / 64000) : ℝ)) ≤ (1157883477307 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4691 / 64000)) (1157883477307 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((988289741 / 500000000) : ℝ) ≤ Real.exp (3 * (3633961689 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3633961689 / 1000000000) / 16) (988289741 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((909399657 / 250000000) : ℝ) / 16) ≤ (123620489 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (909399657 / 250000000) / 16) (123620489 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4659 / 64000) : ℝ) (4691 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3633961689 / 1000000000) (909399657 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4659 / 64000) (4691 / 64000) (1156726172577 / 1000000000000) (1157883477307 / 1000000000000) (3633961689 / 1000000000) (909399657 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4659 / 64000) (4691 / 64000) (3633961689 / 1000000000) (909399657 / 250000000) (18223549 / 1000000000000) (1151467 / 62500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3633961689 / 1000000000) (909399657 / 250000000) (988289741 / 500000000) (123620489 / 62500000) (18223549 / 1000000000000) (1151467 / 62500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0951 :
    ∀ t ∈ Set.Icc ((4691 / 64000) : ℝ) (4723 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((578941738653 / 500000000000) : ℝ) ≤ Real.exp (2 * (4691 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4691 / 64000)) (578941738653 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4723 / 64000) : ℝ)) ≤ (1159041939919 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4723 / 64000)) (1159041939919 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1977927393 / 1000000000) : ℝ) ≤ Real.exp (3 * (3637597469 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3637597469 / 1000000000) / 16) (1977927393 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1820619023 / 500000000) : ℝ) / 16) ≤ (494819501 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1820619023 / 500000000) / 16) (494819501 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4691 / 64000) : ℝ) (4723 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3637597469 / 1000000000) (1820619023 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4691 / 64000) (4723 / 64000) (578941738653 / 500000000000) (1159041939919 / 1000000000000) (3637597469 / 1000000000) (1820619023 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4691 / 64000) (4723 / 64000) (3637597469 / 1000000000) (1820619023 / 500000000) (9012831 / 500000000000) (18223613 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3637597469 / 1000000000) (1820619023 / 500000000) (1977927393 / 1000000000) (494819501 / 250000000) (9012831 / 500000000000) (18223613 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0952 :
    ∀ t ∈ Set.Icc ((4723 / 64000) : ℝ) (951 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((579520969959 / 500000000000) : ℝ) ≤ Real.exp (2 * (4723 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4723 / 64000)) (579520969959 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((951 / 12800) : ℝ)) ≤ (1160201561573 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (951 / 12800)) (1160201561573 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1979277573 / 1000000000) : ℝ) ≤ Real.exp (3 * (1820618443 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1820618443 / 500000000) / 16) (1979277573 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((728976221 / 200000000) : ℝ) / 16) ≤ (1980630459 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (728976221 / 200000000) / 16) (1980630459 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4723 / 64000) : ℝ) (951 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1820618443 / 500000000) (728976221 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4723 / 64000) (951 / 12800) (579520969959 / 500000000000) (1160201561573 / 1000000000000) (1820618443 / 500000000) (728976221 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4723 / 64000) (951 / 12800) (1820618443 / 500000000) (728976221 / 200000000) (17829729 / 1000000000000) (721029 / 40000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1820618443 / 500000000) (728976221 / 200000000) (1979277573 / 1000000000) (1980630459 / 1000000000) (17829729 / 1000000000000) (721029 / 40000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0953 :
    ∀ t ∈ Set.Icc ((951 / 12800) : ℝ) (4787 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((290050390393 / 250000000000) : ℝ) ≤ Real.exp (2 * (951 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (951 / 12800)) (290050390393 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4787 / 64000) : ℝ)) ≤ (1161362343429 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4787 / 64000)) (1161362343429 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((990315013 / 500000000) : ℝ) ≤ Real.exp (3 * (455609993 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (455609993 / 125000000) / 16) (990315013 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3648527809 / 1000000000) : ℝ) / 16) ≤ (247748149 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3648527809 / 1000000000) / 16) (247748149 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((951 / 12800) : ℝ) (4787 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (455609993 / 125000000) (3648527809 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (951 / 12800) (4787 / 64000) (290050390393 / 250000000000) (1161362343429 / 1000000000000) (455609993 / 125000000) (3648527809 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (951 / 12800) (4787 / 64000) (455609993 / 125000000) (3648527809 / 1000000000) (4408933 / 250000000000) (557181 / 31250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (455609993 / 125000000) (3648527809 / 1000000000) (990315013 / 500000000) (247748149 / 125000000) (4408933 / 250000000000) (557181 / 31250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0954 :
    ∀ t ∈ Set.Icc ((4787 / 64000) : ℝ) (4819 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((290340585857 / 250000000000) : ℝ) ≤ Real.exp (2 * (4787 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4787 / 64000)) (290340585857 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4819 / 64000) : ℝ)) ≤ (1162524286647 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4819 / 64000)) (1162524286647 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1981984759 / 1000000000) : ℝ) ≤ Real.exp (3 * (3648526647 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3648526647 / 1000000000) / 16) (1981984759 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1826089081 / 500000000) : ℝ) / 16) ≤ (15494861 / 7812500) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1826089081 / 500000000) / 16) (15494861 / 7812500) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4787 / 64000) : ℝ) (4819 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3648526647 / 1000000000) (1826089081 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4787 / 64000) (4819 / 64000) (290340585857 / 250000000000) (1162524286647 / 1000000000000) (3648526647 / 1000000000) (1826089081 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4787 / 64000) (4819 / 64000) (3648526647 / 1000000000) (1826089081 / 500000000) (2180457 / 125000000000) (3527159 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3648526647 / 1000000000) (1826089081 / 500000000) (1981984759 / 1000000000) (15494861 / 7812500) (2180457 / 125000000000) (3527159 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0955 :
    ∀ t ∈ Set.Icc ((4819 / 64000) : ℝ) (4851 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((581262143323 / 500000000000) : ℝ) ≤ Real.exp (2 * (4819 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4819 / 64000)) (581262143323 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4851 / 64000) : ℝ)) ≤ (116368739239 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4851 / 64000)) (116368739239 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((991670887 / 500000000) : ℝ) ≤ Real.exp (3 * (1826088499 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1826088499 / 500000000) / 16) (991670887 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3655832167 / 1000000000) : ℝ) / 16) ≤ (1984701513 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3655832167 / 1000000000) / 16) (1984701513 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4819 / 64000) : ℝ) (4851 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1826088499 / 500000000) (3655832167 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4819 / 64000) (4851 / 64000) (581262143323 / 500000000000) (116368739239 / 100000000000) (1826088499 / 500000000) (3655832167 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4819 / 64000) (4851 / 64000) (1826088499 / 500000000) (3655832167 / 1000000000) (17253483 / 1000000000000) (8721859 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1826088499 / 500000000) (3655832167 / 1000000000) (991670887 / 500000000) (1984701513 / 1000000000) (17253483 / 1000000000000) (8721859 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0956 :
    ∀ t ∈ Set.Icc ((4851 / 64000) : ℝ) (4883 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1163687392389 / 1000000000000) : ℝ) ≤ Real.exp (2 * (4851 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4851 / 64000)) (1163687392389 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4883 / 64000) : ℝ)) ≤ (58242583091 / 50000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4883 / 64000)) (58242583091 / 50000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((992350539 / 500000000) : ℝ) ≤ Real.exp (3 * (1827915501 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1827915501 / 500000000) / 16) (992350539 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3659489827 / 1000000000) : ℝ) / 16) ≤ (1986063111 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3659489827 / 1000000000) / 16) (1986063111 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4851 / 64000) : ℝ) (4883 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1827915501 / 500000000) (3659489827 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4851 / 64000) (4883 / 64000) (1163687392389 / 1000000000000) (58242583091 / 50000000000) (1827915501 / 500000000) (3659489827 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4851 / 64000) (4883 / 64000) (1827915501 / 500000000) (3659489827 / 1000000000) (4266299 / 250000000000) (2156693 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1827915501 / 500000000) (3659489827 / 1000000000) (992350539 / 500000000) (1986063111 / 1000000000) (4266299 / 250000000000) (2156693 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0957 :
    ∀ t ∈ Set.Icc ((4883 / 64000) : ℝ) (983 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1164851661819 / 1000000000000) : ℝ) ≤ Real.exp (2 * (4883 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4883 / 64000)) (1164851661819 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((983 / 12800) : ℝ)) ≤ (1166017096101 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (983 / 12800)) (1166017096101 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((79442507 / 40000000) : ℝ) ≤ Real.exp (3 * (3659488661 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3659488661 / 1000000000) / 16) (79442507 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3663151147 / 1000000000) : ℝ) / 16) ≤ (993713503 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3663151147 / 1000000000) / 16) (993713503 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4883 / 64000) : ℝ) (983 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3659488661 / 1000000000) (3663151147 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4883 / 64000) (983 / 12800) (1164851661819 / 1000000000000) (1166017096101 / 1000000000000) (3659488661 / 1000000000) (3663151147 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4883 / 64000) (983 / 12800) (3659488661 / 1000000000) (3663151147 / 1000000000) (8439389 / 500000000000) (2133157 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3659488661 / 1000000000) (3663151147 / 1000000000) (79442507 / 40000000) (993713503 / 500000000) (8439389 / 500000000000) (2133157 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0958 :
    ∀ t ∈ Set.Icc ((983 / 12800) : ℝ) (4947 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((11660170961 / 10000000000) : ℝ) ≤ Real.exp (2 * (983 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (983 / 12800)) (11660170961 / 10000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4947 / 64000) : ℝ)) ≤ (2917959241 / 2500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4947 / 64000)) (2917959241 / 2500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((198742657 / 100000000) : ℝ) ≤ Real.exp (3 * (183157499 / 50000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (183157499 / 50000000) / 16) (198742657 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3666816131 / 1000000000) : ℝ) / 16) ≤ (497198301 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3666816131 / 1000000000) / 16) (497198301 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((983 / 12800) : ℝ) (4947 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (183157499 / 50000000) (3666816131 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (983 / 12800) (4947 / 64000) (11660170961 / 10000000000) (2917959241 / 2500000000) (183157499 / 50000000) (3666816131 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (983 / 12800) (4947 / 64000) (183157499 / 50000000) (3666816131 / 1000000000) (16694213 / 1000000000000) (8439419 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (183157499 / 50000000) (3666816131 / 1000000000) (198742657 / 100000000) (497198301 / 250000000) (16694213 / 1000000000000) (8439419 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0959 :
    ∀ t ∈ Set.Icc ((4947 / 64000) : ℝ) (4979 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1167183696399 / 1000000000000) : ℝ) ≤ Real.exp (2 * (4947 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4947 / 64000)) (1167183696399 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4979 / 64000) : ℝ)) ≤ (1168351463883 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4979 / 64000)) (1168351463883 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((31074887 / 15625000) : ℝ) ≤ Real.exp (3 * (3666814963 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3666814963 / 1000000000) / 16) (31074887 / 15625000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3670484781 / 1000000000) : ℝ) / 16) ≤ (199016171 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3670484781 / 1000000000) / 16) (199016171 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4947 / 64000) : ℝ) (4979 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3666814963 / 1000000000) (3670484781 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4947 / 64000) (4979 / 64000) (1167183696399 / 1000000000000) (1168351463883 / 1000000000000) (3666814963 / 1000000000) (3670484781 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4947 / 64000) (4979 / 64000) (3666814963 / 1000000000) (3670484781 / 1000000000) (3302297 / 200000000000) (16694273 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3666814963 / 1000000000) (3670484781 / 1000000000) (31074887 / 15625000) (199016171 / 100000000) (3302297 / 200000000000) (16694273 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch047 :
    ∀ t ∈ Set.Icc ((4451 / 64000) : ℝ) (4979 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0940
      hpThetaDensityTwoTermCompact_cell0941)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0942
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0943
      hpThetaDensityTwoTermCompact_cell0944)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0945
      hpThetaDensityTwoTermCompact_cell0946)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0947
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0948
      hpThetaDensityTwoTermCompact_cell0949))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0950
      hpThetaDensityTwoTermCompact_cell0951)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0952
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0953
      hpThetaDensityTwoTermCompact_cell0954)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0955
      hpThetaDensityTwoTermCompact_cell0956)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0957
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0958
      hpThetaDensityTwoTermCompact_cell0959)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch047
end HodgeProofHP
