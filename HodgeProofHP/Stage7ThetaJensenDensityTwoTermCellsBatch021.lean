/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0420 :
    ∀ t ∈ Set.Icc ((337 / 12800) : ℝ) (1687 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1054067247219 / 1000000000000) : ℝ) ≤ Real.exp (2 * (337 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (337 / 12800)) (1054067247219 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1687 / 64000) : ℝ)) ≤ (527066564241 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1687 / 64000)) (527066564241 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1860595747 / 1000000000) : ℝ) ≤ Real.exp (3 * (3311449231 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3311449231 / 1000000000) / 16) (1860595747 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1655828629 / 500000000) : ℝ) / 16) ≤ (930334161 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1655828629 / 500000000) / 16) (930334161 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((337 / 12800) : ℝ) (1687 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3311449231 / 1000000000) (1655828629 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (337 / 12800) (1687 / 64000) (1054067247219 / 1000000000000) (527066564241 / 500000000000) (3311449231 / 1000000000) (1655828629 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (337 / 12800) (1687 / 64000) (3311449231 / 1000000000) (1655828629 / 500000000) (6056289 / 125000000000) (48480559 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3311449231 / 1000000000) (1655828629 / 500000000) (1860595747 / 1000000000) (930334161 / 500000000) (6056289 / 125000000000) (48480559 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0421 :
    ∀ t ∈ Set.Icc ((1687 / 64000) : ℝ) (1689 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1054133128481 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1687 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1687 / 64000)) (1054133128481 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1689 / 64000) : ℝ)) ≤ (1054199013861 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1689 / 64000)) (1054199013861 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1860667953 / 1000000000) : ℝ) ≤ Real.exp (3 * (3311656203 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3311656203 / 1000000000) / 16) (1860667953 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3311864243 / 1000000000) : ℝ) / 16) ≤ (372148107 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3311864243 / 1000000000) / 16) (372148107 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1687 / 64000) : ℝ) (1689 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3311656203 / 1000000000) (3311864243 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1687 / 64000) (1689 / 64000) (1054133128481 / 1000000000000) (1054199013861 / 1000000000000) (3311656203 / 1000000000) (3311864243 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1687 / 64000) (1689 / 64000) (3311656203 / 1000000000) (3311864243 / 1000000000) (12105059 / 250000000000) (24225233 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3311656203 / 1000000000) (3311864243 / 1000000000) (1860667953 / 1000000000) (372148107 / 200000000) (12105059 / 250000000000) (24225233 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0422 :
    ∀ t ∈ Set.Icc ((1689 / 64000) : ℝ) (1691 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((52709950693 / 50000000000) : ℝ) ≤ Real.exp (2 * (1689 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1689 / 64000)) (52709950693 / 50000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1691 / 64000) : ℝ)) ≤ (1054264903359 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1691 / 64000)) (1054264903359 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((930370083 / 500000000) : ℝ) ≤ Real.exp (3 * (827965797 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (827965797 / 250000000) / 16) (930370083 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3312071241 / 1000000000) : ℝ) / 16) ≤ (465203189 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3312071241 / 1000000000) / 16) (465203189 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1689 / 64000) : ℝ) (1691 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (827965797 / 250000000) (3312071241 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1689 / 64000) (1691 / 64000) (52709950693 / 50000000000) (1054264903359 / 1000000000000) (827965797 / 250000000) (3312071241 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1689 / 64000) (1691 / 64000) (827965797 / 250000000) (3312071241 / 1000000000) (1512193 / 31250000000) (4842039 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (827965797 / 250000000) (3312071241 / 1000000000) (930370083 / 500000000) (465203189 / 250000000) (1512193 / 31250000000) (4842039 / 100000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0423 :
    ∀ t ∈ Set.Icc ((1691 / 64000) : ℝ) (1693 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((527132451679 / 500000000000) : ℝ) ≤ Real.exp (2 * (1691 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1691 / 64000)) (527132451679 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1693 / 64000) : ℝ)) ≤ (527165398487 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1693 / 64000)) (527165398487 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1860812387 / 1000000000) : ℝ) ≤ Real.exp (3 * (1656035093 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1656035093 / 500000000) / 16) (1860812387 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((828069563 / 250000000) : ℝ) / 16) ≤ (232610623 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (828069563 / 250000000) / 16) (232610623 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1691 / 64000) : ℝ) (1693 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1656035093 / 500000000) (828069563 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1691 / 64000) (1693 / 64000) (527132451679 / 500000000000) (527165398487 / 500000000000) (1656035093 / 500000000) (828069563 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1691 / 64000) (1693 / 64000) (1656035093 / 500000000) (828069563 / 250000000) (24180067 / 500000000000) (48390331 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1656035093 / 500000000) (828069563 / 250000000) (1860812387 / 1000000000) (232610623 / 125000000) (24180067 / 500000000000) (48390331 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0424 :
    ∀ t ∈ Set.Icc ((1693 / 64000) : ℝ) (339 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1054330796973 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1693 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1693 / 64000)) (1054330796973 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((339 / 12800) : ℝ)) ≤ (263599173677 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (339 / 12800)) (263599173677 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((372176923 / 200000000) : ℝ) ≤ Real.exp (3 * (3312277197 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3312277197 / 1000000000) / 16) (372176923 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((828121319 / 250000000) : ℝ) / 16) ≤ (93047861 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (828121319 / 250000000) / 16) (93047861 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1693 / 64000) : ℝ) (339 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3312277197 / 1000000000) (828121319 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1693 / 64000) (339 / 12800) (1054330796973 / 1000000000000) (263599173677 / 250000000000) (3312277197 / 1000000000) (828121319 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1693 / 64000) (339 / 12800) (3312277197 / 1000000000) (828121319 / 250000000) (12082527 / 250000000000) (1511259 / 31250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3312277197 / 1000000000) (828121319 / 250000000) (372176923 / 200000000) (93047861 / 50000000) (12082527 / 250000000000) (1511259 / 31250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0425 :
    ∀ t ∈ Set.Icc ((339 / 12800) : ℝ) (1697 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1054396694707 / 1000000000000) : ℝ) ≤ Real.exp (2 * (339 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (339 / 12800)) (1054396694707 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1697 / 64000) : ℝ)) ≤ (1054462596561 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1697 / 64000)) (1054462596561 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((37219137 / 20000000) : ℝ) ≤ Real.exp (3 * (165624211 / 50000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (165624211 / 50000000) / 16) (37219137 / 20000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3312692313 / 1000000000) : ℝ) / 16) ≤ (930514731 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3312692313 / 1000000000) / 16) (930514731 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((339 / 12800) : ℝ) (1697 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (165624211 / 50000000) (3312692313 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (339 / 12800) (1697 / 64000) (1054396694707 / 1000000000000) (1054462596561 / 1000000000000) (165624211 / 50000000) (3312692313 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (339 / 12800) (1697 / 64000) (165624211 / 50000000) (3312692313 / 1000000000) (48300099 / 1000000000000) (24165131 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (165624211 / 50000000) (3312692313 / 1000000000) (37219137 / 20000000) (930514731 / 500000000) (48300099 / 1000000000000) (24165131 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0426 :
    ∀ t ∈ Set.Icc ((1697 / 64000) : ℝ) (1699 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((13180782457 / 12500000000) : ℝ) ≤ Real.exp (2 * (1697 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1697 / 64000)) (13180782457 / 12500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1699 / 64000) : ℝ)) ≤ (1054528502533 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1699 / 64000)) (1054528502533 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1861029093 / 1000000000) : ℝ) ≤ Real.exp (3 * (3312691257 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3312691257 / 1000000000) / 16) (1861029093 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1656449681 / 500000000) : ℝ) / 16) ≤ (116318857 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1656449681 / 500000000) / 16) (116318857 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1697 / 64000) : ℝ) (1699 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3312691257 / 1000000000) (1656449681 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1697 / 64000) (1699 / 64000) (13180782457 / 12500000000) (1054528502533 / 1000000000000) (3312691257 / 1000000000) (1656449681 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1697 / 64000) (1699 / 64000) (3312691257 / 1000000000) (1656449681 / 500000000) (48270107 / 1000000000000) (48300253 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3312691257 / 1000000000) (1656449681 / 500000000) (1861029093 / 1000000000) (116318857 / 62500000) (48270107 / 1000000000000) (48300253 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0427 :
    ∀ t ∈ Set.Icc ((1699 / 64000) : ℝ) (1701 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((263632125633 / 250000000000) : ℝ) ≤ Real.exp (2 * (1699 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1699 / 64000)) (263632125633 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1701 / 64000) : ℝ)) ≤ (65912150789 / 62500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1701 / 64000)) (65912150789 / 62500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1861101343 / 1000000000) : ℝ) ≤ Real.exp (3 * (3312898307 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3312898307 / 1000000000) / 16) (1861101343 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((132524257 / 40000000) : ℝ) / 16) ≤ (1861173969 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (132524257 / 40000000) / 16) (1861173969 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1699 / 64000) : ℝ) (1701 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3312898307 / 1000000000) (132524257 / 40000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1699 / 64000) (1701 / 64000) (263632125633 / 250000000000) (65912150789 / 62500000000) (3312898307 / 1000000000) (132524257 / 40000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1699 / 64000) (1701 / 64000) (3312898307 / 1000000000) (132524257 / 40000000) (48240131 / 1000000000000) (48270261 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3312898307 / 1000000000) (132524257 / 40000000) (1861101343 / 1000000000) (1861173969 / 1000000000) (48240131 / 1000000000000) (48270261 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0428 :
    ∀ t ∈ Set.Icc ((1701 / 64000) : ℝ) (1703 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1054594412623 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1701 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1701 / 64000)) (1054594412623 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1703 / 64000) : ℝ)) ≤ (210932065367 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1703 / 64000)) (210932065367 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((2326467 / 1250000) : ℝ) ≤ Real.exp (3 * (3313105369 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3313105369 / 1000000000) / 16) (2326467 / 1250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3313313501 / 1000000000) : ℝ) / 16) ≤ (930623117 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3313313501 / 1000000000) / 16) (930623117 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1701 / 64000) : ℝ) (1703 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3313105369 / 1000000000) (3313313501 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1701 / 64000) (1703 / 64000) (1054594412623 / 1000000000000) (210932065367 / 200000000000) (3313105369 / 1000000000) (3313313501 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1701 / 64000) (1703 / 64000) (3313105369 / 1000000000) (3313313501 / 1000000000) (12052543 / 250000000000) (9648057 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3313105369 / 1000000000) (3313313501 / 1000000000) (2326467 / 1250000) (930623117 / 500000000) (12052543 / 250000000000) (9648057 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0429 :
    ∀ t ∈ Set.Icc ((1703 / 64000) : ℝ) (341 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((527330163417 / 500000000000) : ℝ) ≤ Real.exp (2 * (1703 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1703 / 64000)) (527330163417 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((341 / 12800) : ℝ)) ≤ (210945249033 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (341 / 12800)) (210945249033 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((372249173 / 200000000) : ℝ) ≤ Real.exp (3 * (662662489 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (662662489 / 200000000) / 16) (372249173 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3313520589 / 1000000000) : ℝ) / 16) ≤ (930659253 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3313520589 / 1000000000) / 16) (930659253 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1703 / 64000) : ℝ) (341 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (662662489 / 200000000) (3313520589 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1703 / 64000) (341 / 12800) (527330163417 / 500000000000) (210945249033 / 200000000000) (662662489 / 200000000) (3313520589 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1703 / 64000) (341 / 12800) (662662489 / 200000000) (3313520589 / 1000000000) (4818023 / 100000000000) (24105163 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (662662489 / 200000000) (3313520589 / 1000000000) (372249173 / 200000000) (930659253 / 500000000) (4818023 / 100000000000) (24105163 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0430 :
    ∀ t ∈ Set.Icc ((341 / 12800) : ℝ) (1707 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((263681561291 / 250000000000) : ℝ) ≤ Real.exp (2 * (341 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (341 / 12800)) (263681561291 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1707 / 64000) : ℝ)) ≤ (210958433523 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1707 / 64000)) (210958433523 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((232664767 / 125000000) : ℝ) ≤ Real.exp (3 * (3313519533 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3313519533 / 1000000000) / 16) (232664767 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3313727691 / 1000000000) : ℝ) / 16) ≤ (372278157 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3313727691 / 1000000000) / 16) (372278157 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((341 / 12800) : ℝ) (1707 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3313519533 / 1000000000) (3313727691 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (341 / 12800) (1707 / 64000) (263681561291 / 250000000000) (210958433523 / 200000000000) (3313519533 / 1000000000) (3313727691 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (341 / 12800) (1707 / 64000) (3313519533 / 1000000000) (3313727691 / 1000000000) (9630061 / 200000000000) (1505637 / 31250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3313519533 / 1000000000) (3313727691 / 1000000000) (232664767 / 125000000) (372278157 / 200000000) (9630061 / 200000000000) (1505637 / 31250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0431 :
    ∀ t ∈ Set.Icc ((1707 / 64000) : ℝ) (1709 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((527396083807 / 500000000000) : ℝ) ≤ Real.exp (2 * (1707 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1707 / 64000)) (527396083807 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1709 / 64000) : ℝ)) ≤ (527429047093 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1709 / 64000)) (527429047093 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((116336901 / 62500000) : ℝ) ≤ Real.exp (3 * (662745327 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (662745327 / 200000000) / 16) (116336901 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((662786961 / 200000000) : ℝ) / 16) ≤ (58170721 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (662786961 / 200000000) / 16) (58170721 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1707 / 64000) : ℝ) (1709 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (662745327 / 200000000) (662786961 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1707 / 64000) (1709 / 64000) (527396083807 / 500000000000) (527429047093 / 500000000000) (662745327 / 200000000) (662786961 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1707 / 64000) (1709 / 64000) (662745327 / 200000000) (662786961 / 200000000) (12030099 / 250000000000) (48150459 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (662745327 / 200000000) (662786961 / 200000000) (116336901 / 62500000) (58170721 / 31250000) (12030099 / 250000000000) (48150459 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0432 :
    ∀ t ∈ Set.Icc ((1709 / 64000) : ℝ) (1711 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((210971618837 / 200000000000) : ℝ) ≤ Real.exp (2 * (1709 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1709 / 64000)) (210971618837 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1711 / 64000) : ℝ)) ≤ (1054924024877 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1711 / 64000)) (1054924024877 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((930731351 / 500000000) : ℝ) ≤ Real.exp (3 * (3313933749 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3313933749 / 1000000000) / 16) (930731351 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3314141933 / 1000000000) : ℝ) / 16) ≤ (930767683 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3314141933 / 1000000000) / 16) (930767683 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1709 / 64000) : ℝ) (1711 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3313933749 / 1000000000) (3314141933 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1709 / 64000) (1711 / 64000) (210971618837 / 200000000000) (1054924024877 / 1000000000000) (3313933749 / 1000000000) (3314141933 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1709 / 64000) (1711 / 64000) (3313933749 / 1000000000) (3314141933 / 1000000000) (6011313 / 125000000000) (962411 / 20000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3313933749 / 1000000000) (3314141933 / 1000000000) (930731351 / 500000000) (930767683 / 500000000) (6011313 / 125000000000) (962411 / 20000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0433 :
    ∀ t ∈ Set.Icc ((1711 / 64000) : ℝ) (1713 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((263731006219 / 250000000000) : ℝ) ≤ Real.exp (2 * (1711 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1711 / 64000)) (263731006219 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1713 / 64000) : ℝ)) ≤ (1054989959689 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1713 / 64000)) (1054989959689 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((465383749 / 250000000) : ℝ) ≤ Real.exp (3 * (3314140877 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3314140877 / 1000000000) / 16) (465383749 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3314349073 / 1000000000) : ℝ) / 16) ≤ (1861607667 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3314349073 / 1000000000) / 16) (1861607667 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1711 / 64000) : ℝ) (1713 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3314140877 / 1000000000) (3314349073 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1711 / 64000) (1713 / 64000) (263731006219 / 250000000000) (1054989959689 / 1000000000000) (3314140877 / 1000000000) (3314349073 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1711 / 64000) (1713 / 64000) (3314140877 / 1000000000) (3314349073 / 1000000000) (48060629 / 1000000000000) (24045329 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3314140877 / 1000000000) (3314349073 / 1000000000) (465383749 / 250000000) (1861607667 / 1000000000) (48060629 / 1000000000000) (24045329 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0434 :
    ∀ t ∈ Set.Icc ((1713 / 64000) : ℝ) (343 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((131873744961 / 125000000000) : ℝ) ≤ Real.exp (2 * (1713 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1713 / 64000)) (131873744961 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((343 / 12800) : ℝ)) ≤ (527527949311 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (343 / 12800)) (527527949311 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1861607297 / 1000000000) : ℝ) ≤ Real.exp (3 * (3314348017 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3314348017 / 1000000000) / 16) (1861607297 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1657278113 / 500000000) : ℝ) / 16) ≤ (74467199 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1657278113 / 500000000) / 16) (74467199 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1713 / 64000) : ℝ) (343 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3314348017 / 1000000000) (1657278113 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1713 / 64000) (343 / 12800) (131873744961 / 125000000000) (527527949311 / 500000000000) (3314348017 / 1000000000) (1657278113 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1713 / 64000) (343 / 12800) (3314348017 / 1000000000) (1657278113 / 500000000) (48030771 / 1000000000000) (48060783 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3314348017 / 1000000000) (1657278113 / 500000000) (1861607297 / 1000000000) (74467199 / 40000000) (48030771 / 1000000000000) (48060783 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0435 :
    ∀ t ∈ Set.Icc ((343 / 12800) : ℝ) (1717 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1055055898621 / 1000000000000) : ℝ) ≤ Real.exp (2 * (343 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (343 / 12800)) (1055055898621 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1717 / 64000) : ℝ)) ≤ (1055121841677 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1717 / 64000)) (1055121841677 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((930839803 / 500000000) : ℝ) ≤ Real.exp (3 * (331455517 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (331455517 / 100000000) / 16) (930839803 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((25896589 / 7812500) : ℝ) / 16) ≤ (1861752291 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (25896589 / 7812500) / 16) (1861752291 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((343 / 12800) : ℝ) (1717 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (331455517 / 100000000) (25896589 / 7812500) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (343 / 12800) (1717 / 64000) (1055055898621 / 1000000000000) (1055121841677 / 1000000000000) (331455517 / 100000000) (25896589 / 7812500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (343 / 12800) (1717 / 64000) (331455517 / 100000000) (25896589 / 7812500) (48000929 / 1000000000000) (12007731 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (331455517 / 100000000) (25896589 / 7812500) (930839803 / 500000000) (1861752291 / 1000000000) (48000929 / 1000000000000) (12007731 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0436 :
    ∀ t ∈ Set.Icc ((1717 / 64000) : ℝ) (1719 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((263780460419 / 250000000000) : ℝ) ≤ Real.exp (2 * (1717 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1717 / 64000)) (263780460419 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1719 / 64000) : ℝ)) ≤ (1055187788853 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1719 / 64000)) (1055187788853 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((930875961 / 500000000) : ℝ) ≤ Real.exp (3 * (103586323 / 31250000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (103586323 / 31250000) / 16) (930875961 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((828742643 / 250000000) : ℝ) / 16) ≤ (372364923 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (828742643 / 250000000) / 16) (372364923 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1717 / 64000) : ℝ) (1719 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (103586323 / 31250000) (828742643 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1717 / 64000) (1719 / 64000) (263780460419 / 250000000000) (1055187788853 / 1000000000000) (103586323 / 31250000) (828742643 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1717 / 64000) (1719 / 64000) (103586323 / 31250000) (828742643 / 250000000) (1499097 / 31250000000) (24000541 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (103586323 / 31250000) (828742643 / 250000000) (930875961 / 500000000) (372364923 / 200000000) (1499097 / 31250000000) (24000541 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0437 :
    ∀ t ∈ Set.Icc ((1719 / 64000) : ℝ) (1721 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((263796947213 / 250000000000) : ℝ) ≤ Real.exp (2 * (1719 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1719 / 64000)) (263796947213 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1721 / 64000) : ℝ)) ≤ (21105074803 / 20000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1721 / 64000)) (21105074803 / 20000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((372364849 / 200000000) : ℝ) ≤ Real.exp (3 * (662993903 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (662993903 / 200000000) / 16) (372364849 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((828794441 / 250000000) : ℝ) / 16) ≤ (372379389 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (828794441 / 250000000) / 16) (372379389 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1719 / 64000) : ℝ) (1721 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (662993903 / 200000000) (828794441 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1719 / 64000) (1721 / 64000) (263796947213 / 250000000000) (21105074803 / 20000000000) (662993903 / 200000000) (828794441 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1719 / 64000) (1721 / 64000) (662993903 / 200000000) (828794441 / 250000000) (2996331 / 62500000000) (47971257 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (662993903 / 200000000) (828794441 / 250000000) (372364849 / 200000000) (372379389 / 200000000) (2996331 / 62500000000) (47971257 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0438 :
    ∀ t ∈ Set.Icc ((1721 / 64000) : ℝ) (1723 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1055253740149 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1721 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1721 / 64000)) (1055253740149 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1723 / 64000) : ℝ)) ≤ (105531969557 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1723 / 64000)) (105531969557 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((14546067 / 7812500) : ℝ) ≤ Real.exp (3 * (828794177 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (828794177 / 250000000) / 16) (14546067 / 7812500) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3315384969 / 1000000000) : ℝ) / 16) ≤ (1861969283 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3315384969 / 1000000000) / 16) (1861969283 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1721 / 64000) : ℝ) (1723 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (828794177 / 250000000) (3315384969 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1721 / 64000) (1723 / 64000) (1055253740149 / 1000000000000) (105531969557 / 100000000000) (828794177 / 250000000) (3315384969 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1721 / 64000) (1723 / 64000) (828794177 / 250000000) (3315384969 / 1000000000) (2994469 / 62500000000) (47941449 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (828794177 / 250000000) (3315384969 / 1000000000) (14546067 / 7812500) (1861969283 / 1000000000) (2994469 / 62500000000) (47941449 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0439 :
    ∀ t ∈ Set.Icc ((1723 / 64000) : ℝ) (69 / 2560), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1055319695569 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1723 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1723 / 64000)) (1055319695569 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((69 / 2560) : ℝ)) ≤ (131923206889 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (69 / 2560)) (131923206889 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1861968913 / 1000000000) : ℝ) ≤ Real.exp (3 * (3315383913 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3315383913 / 1000000000) / 16) (1861968913 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3315592187 / 1000000000) : ℝ) / 16) ≤ (465510407 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3315592187 / 1000000000) / 16) (465510407 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1723 / 64000) : ℝ) (69 / 2560),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3315383913 / 1000000000) (3315592187 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1723 / 64000) (69 / 2560) (1055319695569 / 1000000000000) (131923206889 / 125000000000) (3315383913 / 1000000000) (3315592187 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1723 / 64000) (69 / 2560) (3315383913 / 1000000000) (3315592187 / 1000000000) (47881729 / 1000000000000) (47911657 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3315383913 / 1000000000) (3315592187 / 1000000000) (1861968913 / 1000000000) (465510407 / 250000000) (47881729 / 1000000000000) (47911657 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch021 :
    ∀ t ∈ Set.Icc ((337 / 12800) : ℝ) (69 / 2560),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0420
      hpThetaDensityTwoTermCompact_cell0421)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0422
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0423
      hpThetaDensityTwoTermCompact_cell0424)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0425
      hpThetaDensityTwoTermCompact_cell0426)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0427
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0428
      hpThetaDensityTwoTermCompact_cell0429))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0430
      hpThetaDensityTwoTermCompact_cell0431)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0432
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0433
      hpThetaDensityTwoTermCompact_cell0434)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0435
      hpThetaDensityTwoTermCompact_cell0436)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0437
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0438
      hpThetaDensityTwoTermCompact_cell0439)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch021
end HodgeProofHP
