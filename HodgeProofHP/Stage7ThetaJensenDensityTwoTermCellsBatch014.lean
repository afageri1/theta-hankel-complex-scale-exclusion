/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0280 :
    ∀ t ∈ Set.Icc ((1529 / 64000) : ℝ) (153 / 6400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((131117646793 / 125000000000) : ℝ) ≤ Real.exp (2 * (1529 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1529 / 64000)) (131117646793 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((153 / 6400) : ℝ)) ≤ (262243488567 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (153 / 6400)) (262243488567 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1854986141 / 1000000000) : ℝ) ≤ Real.exp (3 * (3295345201 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3295345201 / 1000000000) / 16) (1854986141 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((205965577 / 62500000) : ℝ) / 16) ≤ (74200893 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (205965577 / 62500000) / 16) (74200893 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1529 / 64000) : ℝ) (153 / 6400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3295345201 / 1000000000) (205965577 / 62500000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1529 / 64000) (153 / 6400) (131117646793 / 125000000000) (262243488567 / 250000000000) (3295345201 / 1000000000) (205965577 / 62500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1529 / 64000) (153 / 6400) (3295345201 / 1000000000) (205965577 / 62500000) (50864379 / 1000000000000) (50880257 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3295345201 / 1000000000) (205965577 / 62500000) (1854986141 / 1000000000) (74200893 / 40000000) (50864379 / 1000000000000) (50880257 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0281 :
    ∀ t ∈ Set.Icc ((153 / 6400) : ℝ) (1531 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1048973954267 / 1000000000000) : ℝ) ≤ Real.exp (2 * (153 / 6400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (153 / 6400)) (1048973954267 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1531 / 64000) : ℝ)) ≤ (1049006735217 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1531 / 64000)) (1049006735217 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1855021959 / 1000000000) : ℝ) ≤ Real.exp (3 * (1647724091 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1647724091 / 500000000) / 16) (1855021959 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3295552217 / 1000000000) : ℝ) / 16) ≤ (927529073 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3295552217 / 1000000000) / 16) (927529073 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((153 / 6400) : ℝ) (1531 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1647724091 / 500000000) (3295552217 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (153 / 6400) (1531 / 64000) (1048973954267 / 1000000000000) (1049006735217 / 1000000000000) (1647724091 / 500000000) (3295552217 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (153 / 6400) (1531 / 64000) (1647724091 / 500000000) (3295552217 / 1000000000) (25424333 / 500000000000) (2543227 / 50000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1647724091 / 500000000) (3295552217 / 1000000000) (1855021959 / 1000000000) (927529073 / 500000000) (25424333 / 500000000000) (2543227 / 50000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0282 :
    ∀ t ∈ Set.Icc ((1531 / 64000) : ℝ) (383 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((65562920951 / 62500000000) : ℝ) ≤ Real.exp (2 * (1531 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1531 / 64000)) (65562920951 / 62500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((383 / 16000) : ℝ)) ≤ (1049039517189 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (383 / 16000)) (1049039517189 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1855057779 / 1000000000) : ℝ) ≤ Real.exp (3 * (3295551167 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3295551167 / 1000000000) / 16) (1855057779 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((823913801 / 250000000) : ℝ) / 16) ≤ (1855093967 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (823913801 / 250000000) / 16) (1855093967 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1531 / 64000) : ℝ) (383 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3295551167 / 1000000000) (823913801 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1531 / 64000) (383 / 16000) (65562920951 / 62500000000) (1049039517189 / 1000000000000) (3295551167 / 1000000000) (823913801 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1531 / 64000) (383 / 16000) (3295551167 / 1000000000) (823913801 / 250000000) (50832959 / 1000000000000) (12712207 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3295551167 / 1000000000) (823913801 / 250000000) (1855057779 / 1000000000) (1855093967 / 1000000000) (50832959 / 1000000000000) (12712207 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0283 :
    ∀ t ∈ Set.Icc ((383 / 16000) : ℝ) (1533 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((262259879297 / 250000000000) : ℝ) ≤ Real.exp (2 * (383 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (383 / 16000)) (262259879297 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1533 / 64000) : ℝ)) ≤ (1049072300187 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1533 / 64000)) (1049072300187 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1855093601 / 1000000000) : ℝ) ≤ Real.exp (3 * (1647827077 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1647827077 / 500000000) / 16) (1855093601 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((659151639 / 200000000) : ℝ) / 16) ≤ (1855129791 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (659151639 / 200000000) / 16) (1855129791 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((383 / 16000) : ℝ) (1533 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1647827077 / 500000000) (659151639 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (383 / 16000) (1533 / 64000) (262259879297 / 250000000000) (1049072300187 / 1000000000000) (1647827077 / 500000000) (659151639 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (383 / 16000) (1533 / 64000) (1647827077 / 500000000) (659151639 / 200000000) (10163451 / 200000000000) (317707 / 6250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1647827077 / 500000000) (659151639 / 200000000) (1855093601 / 1000000000) (1855129791 / 1000000000) (10163451 / 200000000000) (317707 / 6250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0284 :
    ∀ t ∈ Set.Icc ((1533 / 64000) : ℝ) (767 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((524536150093 / 500000000000) : ℝ) ≤ Real.exp (2 * (1533 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1533 / 64000)) (524536150093 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((767 / 32000) : ℝ)) ≤ (65569067763 / 62500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (767 / 32000)) (65569067763 / 62500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((74205177 / 40000000) : ℝ) ≤ Real.exp (3 * (659151429 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (659151429 / 200000000) / 16) (74205177 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3295861189 / 1000000000) : ℝ) / 16) ≤ (1855165617 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3295861189 / 1000000000) / 16) (1855165617 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1533 / 64000) : ℝ) (767 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (659151429 / 200000000) (3295861189 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1533 / 64000) (767 / 32000) (524536150093 / 500000000000) (65569067763 / 62500000000) (659151429 / 200000000) (3295861189 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1533 / 64000) (767 / 32000) (659151429 / 200000000) (3295861189 / 1000000000) (10160311 / 200000000000) (6352177 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (659151429 / 200000000) (3295861189 / 1000000000) (74205177 / 40000000) (1855165617 / 1000000000) (10160311 / 200000000000) (6352177 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0285 :
    ∀ t ∈ Set.Icc ((767 / 32000) : ℝ) (307 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1049105084207 / 1000000000000) : ℝ) ≤ Real.exp (2 * (767 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (767 / 32000)) (1049105084207 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((307 / 12800) : ℝ)) ≤ (524568934627 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (307 / 12800)) (524568934627 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((7420661 / 4000000) : ℝ) ≤ Real.exp (3 * (3295860139 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3295860139 / 1000000000) / 16) (7420661 / 4000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3295964187 / 1000000000) : ℝ) / 16) ≤ (463800361 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3295964187 / 1000000000) / 16) (463800361 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((767 / 32000) : ℝ) (307 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3295860139 / 1000000000) (3295964187 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (767 / 32000) (307 / 12800) (1049105084207 / 1000000000000) (524568934627 / 500000000000) (3295860139 / 1000000000) (3295964187 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (767 / 32000) (307 / 12800) (3295860139 / 1000000000) (3295964187 / 1000000000) (50785861 / 1000000000000) (50801717 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3295860139 / 1000000000) (3295964187 / 1000000000) (7420661 / 4000000) (463800361 / 250000000) (50785861 / 1000000000000) (50801717 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0286 :
    ∀ t ∈ Set.Icc ((307 / 12800) : ℝ) (3 / 125), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1049137869253 / 1000000000000) : ℝ) ≤ Real.exp (2 * (307 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (307 / 12800)) (1049137869253 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3 / 125) : ℝ)) ≤ (41966826213 / 40000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3 / 125)) (41966826213 / 40000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1855201077 / 1000000000) : ℝ) ≤ Real.exp (3 * (6437428 / 1953125) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6437428 / 1953125) / 16) (1855201077 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3296067187 / 1000000000) : ℝ) / 16) ≤ (1855237273 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3296067187 / 1000000000) / 16) (1855237273 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((307 / 12800) : ℝ) (3 / 125),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6437428 / 1953125) (3296067187 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (307 / 12800) (3 / 125) (1049137869253 / 1000000000000) (41966826213 / 40000000000) (6437428 / 1953125) (3296067187 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (307 / 12800) (3 / 125) (6437428 / 1953125) (3296067187 / 1000000000) (5077017 / 100000000000) (25393011 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (6437428 / 1953125) (3296067187 / 1000000000) (1855201077 / 1000000000) (1855237273 / 1000000000) (5077017 / 100000000000) (25393011 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0287 :
    ∀ t ∈ Set.Icc ((3 / 125) : ℝ) (1537 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((262292663831 / 250000000000) : ℝ) ≤ Real.exp (2 * (3 / 125)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3 / 125)) (262292663831 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1537 / 64000) : ℝ)) ≤ (52460172121 / 50000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1537 / 64000)) (52460172121 / 50000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1855236907 / 1000000000) : ℝ) ≤ Real.exp (3 * (3296066137 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3296066137 / 1000000000) / 16) (1855236907 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3296170191 / 1000000000) : ℝ) / 16) ≤ (115954569 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3296170191 / 1000000000) / 16) (115954569 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3 / 125) : ℝ) (1537 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3296066137 / 1000000000) (3296170191 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3 / 125) (1537 / 64000) (262292663831 / 250000000000) (52460172121 / 50000000000) (3296066137 / 1000000000) (3296170191 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3 / 125) (1537 / 64000) (3296066137 / 1000000000) (3296170191 / 1000000000) (12688621 / 250000000000) (12692583 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3296066137 / 1000000000) (3296170191 / 1000000000) (1855236907 / 1000000000) (115954569 / 62500000) (12688621 / 250000000000) (12692583 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0288 :
    ∀ t ∈ Set.Icc ((1537 / 64000) : ℝ) (769 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1049203442419 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1537 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1537 / 64000)) (1049203442419 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((769 / 32000) : ℝ)) ≤ (52461811527 / 50000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (769 / 32000)) (52461811527 / 50000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((927636369 / 500000000) : ℝ) ≤ Real.exp (3 * (3296169141 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3296169141 / 1000000000) / 16) (927636369 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1648136599 / 500000000) : ℝ) / 16) ≤ (1855308937 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1648136599 / 500000000) / 16) (1855308937 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1537 / 64000) : ℝ) (769 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3296169141 / 1000000000) (1648136599 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1537 / 64000) (769 / 32000) (1049203442419 / 1000000000000) (52461811527 / 50000000000) (3296169141 / 1000000000) (1648136599 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1537 / 64000) (769 / 32000) (3296169141 / 1000000000) (1648136599 / 500000000) (25369401 / 500000000000) (10150929 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3296169141 / 1000000000) (1648136599 / 500000000) (927636369 / 500000000) (1855308937 / 1000000000) (25369401 / 500000000000) (10150929 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0289 :
    ∀ t ∈ Set.Icc ((769 / 32000) : ℝ) (1539 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1049236230539 / 1000000000000) : ℝ) ≤ Real.exp (2 * (769 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (769 / 32000)) (1049236230539 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1539 / 64000) : ℝ)) ≤ (209853803937 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1539 / 64000)) (209853803937 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((185530857 / 100000000) : ℝ) ≤ Real.exp (3 * (3296272147 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3296272147 / 1000000000) / 16) (185530857 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((206023513 / 62500000) : ℝ) / 16) ≤ (1855344771 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (206023513 / 62500000) / 16) (1855344771 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((769 / 32000) : ℝ) (1539 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3296272147 / 1000000000) (206023513 / 62500000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (769 / 32000) (1539 / 64000) (1049236230539 / 1000000000000) (209853803937 / 200000000000) (3296272147 / 1000000000) (206023513 / 62500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (769 / 32000) (1539 / 64000) (3296272147 / 1000000000) (206023513 / 62500000) (81157 / 1600000000) (12684741 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3296272147 / 1000000000) (206023513 / 62500000) (185530857 / 100000000) (1855344771 / 1000000000) (81157 / 1600000000) (12684741 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0290 :
    ∀ t ∈ Set.Icc ((1539 / 64000) : ℝ) (77 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((262317254921 / 250000000000) : ℝ) ≤ Real.exp (2 * (1539 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1539 / 64000)) (262317254921 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((77 / 3200) : ℝ)) ≤ (524650904927 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (77 / 3200)) (524650904927 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((371068881 / 200000000) : ℝ) ≤ Real.exp (3 * (1648187579 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1648187579 / 500000000) / 16) (371068881 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3296479221 / 1000000000) : ℝ) / 16) ≤ (1855380607 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3296479221 / 1000000000) / 16) (1855380607 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1539 / 64000) : ℝ) (77 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1648187579 / 500000000) (3296479221 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1539 / 64000) (77 / 3200) (262317254921 / 250000000000) (524650904927 / 500000000000) (1648187579 / 500000000) (3296479221 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1539 / 64000) (77 / 3200) (1648187579 / 500000000) (3296479221 / 1000000000) (12676863 / 250000000000) (25361643 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1648187579 / 500000000) (3296479221 / 1000000000) (371068881 / 200000000) (1855380607 / 1000000000) (12676863 / 250000000000) (25361643 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0291 :
    ∀ t ∈ Set.Icc ((77 / 3200) : ℝ) (1541 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1049301809853 / 1000000000000) : ℝ) ≤ Real.exp (2 * (77 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (77 / 3200)) (1049301809853 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1541 / 64000) : ℝ)) ≤ (131166825131 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1541 / 64000)) (131166825131 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1855380241 / 1000000000) : ℝ) ≤ Real.exp (3 * (3296478171 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3296478171 / 1000000000) / 16) (1855380241 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1648291119 / 500000000) : ℝ) / 16) ≤ (927708223 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1648291119 / 500000000) / 16) (927708223 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((77 / 3200) : ℝ) (1541 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3296478171 / 1000000000) (1648291119 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (77 / 3200) (1541 / 64000) (1049301809853 / 1000000000000) (131166825131 / 125000000000) (3296478171 / 1000000000) (1648291119 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (77 / 3200) (1541 / 64000) (3296478171 / 1000000000) (1648291119 / 500000000) (50691783 / 1000000000000) (50707613 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3296478171 / 1000000000) (1648291119 / 500000000) (1855380241 / 1000000000) (927708223 / 500000000) (50691783 / 1000000000000) (50707613 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0292 :
    ∀ t ∈ Set.Icc ((1541 / 64000) : ℝ) (771 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1049334601047 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1541 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1541 / 64000)) (1049334601047 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((771 / 32000) : ℝ)) ≤ (524683696633 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (771 / 32000)) (524683696633 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1855416079 / 1000000000) : ℝ) ≤ Real.exp (3 * (3296581187 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3296581187 / 1000000000) / 16) (1855416079 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1648342629 / 500000000) : ℝ) / 16) ≤ (927726143 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1648342629 / 500000000) / 16) (927726143 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1541 / 64000) : ℝ) (771 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3296581187 / 1000000000) (1648342629 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1541 / 64000) (771 / 32000) (1049334601047 / 1000000000000) (524683696633 / 500000000000) (3296581187 / 1000000000) (1648342629 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1541 / 64000) (771 / 32000) (3296581187 / 1000000000) (1648342629 / 500000000) (50676119 / 1000000000000) (6336493 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3296581187 / 1000000000) (1648342629 / 500000000) (1855416079 / 1000000000) (927726143 / 500000000) (50676119 / 1000000000000) (6336493 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0293 :
    ∀ t ∈ Set.Icc ((771 / 32000) : ℝ) (1543 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((209873478653 / 200000000000) : ℝ) ≤ Real.exp (2 * (771 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (771 / 32000)) (209873478653 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1543 / 64000) : ℝ)) ≤ (104940018651 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1543 / 64000)) (104940018651 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1855451919 / 1000000000) : ℝ) ≤ Real.exp (3 * (3296684207 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3296684207 / 1000000000) / 16) (1855451919 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3296788281 / 1000000000) : ℝ) / 16) ≤ (14496001 / 7812500) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3296788281 / 1000000000) / 16) (14496001 / 7812500) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((771 / 32000) : ℝ) (1543 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3296684207 / 1000000000) (3296788281 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (771 / 32000) (1543 / 64000) (209873478653 / 200000000000) (104940018651 / 100000000000) (3296684207 / 1000000000) (3296788281 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (771 / 32000) (1543 / 64000) (3296684207 / 1000000000) (3296788281 / 1000000000) (50660459 / 1000000000000) (1266907 / 25000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3296684207 / 1000000000) (3296788281 / 1000000000) (1855451919 / 1000000000) (14496001 / 7812500) (50660459 / 1000000000000) (1266907 / 25000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0294 :
    ∀ t ∈ Set.Icc ((1543 / 64000) : ℝ) (193 / 8000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1049400186509 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1543 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1543 / 64000)) (1049400186509 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((193 / 8000) : ℝ)) ≤ (524716490389 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (193 / 8000)) (524716490389 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1855487761 / 1000000000) : ℝ) ≤ Real.exp (3 * (329678723 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (329678723 / 100000000) / 16) (1855487761 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3296891307 / 1000000000) : ℝ) / 16) ≤ (1855523971 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3296891307 / 1000000000) / 16) (1855523971 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1543 / 64000) : ℝ) (193 / 8000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (329678723 / 100000000) (3296891307 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1543 / 64000) (193 / 8000) (1049400186509 / 1000000000000) (524716490389 / 500000000000) (329678723 / 100000000) (3296891307 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1543 / 64000) (193 / 8000) (329678723 / 100000000) (3296891307 / 1000000000) (50644803 / 1000000000000) (2533031 / 50000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (329678723 / 100000000) (3296891307 / 1000000000) (1855487761 / 1000000000) (1855523971 / 1000000000) (50644803 / 1000000000000) (2533031 / 50000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0295 :
    ∀ t ∈ Set.Icc ((193 / 8000) : ℝ) (309 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1049432980777 / 1000000000000) : ℝ) ≤ Real.exp (2 * (193 / 8000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (193 / 8000)) (1049432980777 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((309 / 12800) : ℝ)) ≤ (1049465776071 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (309 / 12800)) (1049465776071 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((463880901 / 250000000) : ℝ) ≤ Real.exp (3 * (206055641 / 62500000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (206055641 / 62500000) / 16) (463880901 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((103031073 / 31250000) : ℝ) / 16) ≤ (231944977 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (103031073 / 31250000) / 16) (231944977 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((193 / 8000) : ℝ) (309 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (206055641 / 62500000) (103031073 / 31250000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (193 / 8000) (309 / 12800) (1049432980777 / 1000000000000) (1049465776071 / 1000000000000) (206055641 / 62500000) (103031073 / 31250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (193 / 8000) (309 / 12800) (206055641 / 62500000) (103031073 / 31250000) (1582161 / 31250000000) (12661241 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (206055641 / 62500000) (103031073 / 31250000) (463880901 / 250000000) (231944977 / 125000000) (1582161 / 31250000000) (12661241 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0296 :
    ∀ t ∈ Set.Icc ((309 / 12800) : ℝ) (773 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((104946577607 / 100000000000) : ℝ) ≤ Real.exp (2 * (309 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (309 / 12800)) (104946577607 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((773 / 32000) : ℝ)) ≤ (1049498572389 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (773 / 32000)) (1049498572389 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((37111189 / 20000000) : ℝ) ≤ Real.exp (3 * (1648496643 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1648496643 / 500000000) / 16) (37111189 / 20000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3297097369 / 1000000000) : ℝ) / 16) ≤ (115974729 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3297097369 / 1000000000) / 16) (115974729 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((309 / 12800) : ℝ) (773 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1648496643 / 500000000) (3297097369 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (309 / 12800) (773 / 32000) (104946577607 / 100000000000) (1049498572389 / 1000000000000) (1648496643 / 500000000) (3297097369 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (309 / 12800) (773 / 32000) (1648496643 / 500000000) (3297097369 / 1000000000) (10122701 / 200000000000) (50629313 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1648496643 / 500000000) (3297097369 / 1000000000) (37111189 / 20000000) (115974729 / 62500000) (10122701 / 200000000000) (50629313 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0297 :
    ∀ t ∈ Set.Icc ((773 / 32000) : ℝ) (1547 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((262374643097 / 250000000000) : ℝ) ≤ Real.exp (2 * (773 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (773 / 32000)) (262374643097 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1547 / 64000) : ℝ)) ≤ (262382842433 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1547 / 64000)) (262382842433 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1855595297 / 1000000000) : ℝ) ≤ Real.exp (3 * (3297096319 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3297096319 / 1000000000) / 16) (1855595297 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((659440081 / 200000000) : ℝ) / 16) ≤ (1855631513 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (659440081 / 200000000) / 16) (1855631513 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((773 / 32000) : ℝ) (1547 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3297096319 / 1000000000) (659440081 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (773 / 32000) (1547 / 64000) (262374643097 / 250000000000) (262382842433 / 250000000000) (3297096319 / 1000000000) (659440081 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (773 / 32000) (1547 / 64000) (3297096319 / 1000000000) (659440081 / 200000000) (25298931 / 500000000000) (25306833 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3297096319 / 1000000000) (659440081 / 200000000) (1855595297 / 1000000000) (1855631513 / 1000000000) (25298931 / 500000000000) (25306833 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0298 :
    ∀ t ∈ Set.Icc ((1547 / 64000) : ℝ) (387 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1049531369731 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1547 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1547 / 64000)) (1049531369731 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((387 / 16000) : ℝ)) ≤ (10495641681 / 10000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (387 / 16000)) (10495641681 / 10000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((927815573 / 500000000) : ℝ) ≤ Real.exp (3 * (1648599677 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1648599677 / 500000000) / 16) (927815573 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((824325861 / 250000000) : ℝ) / 16) ≤ (1855667363 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (824325861 / 250000000) / 16) (1855667363 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1547 / 64000) : ℝ) (387 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1648599677 / 500000000) (824325861 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1547 / 64000) (387 / 16000) (1049531369731 / 1000000000000) (10495641681 / 10000000000) (1648599677 / 500000000) (824325861 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1547 / 64000) (387 / 16000) (1648599677 / 500000000) (824325861 / 250000000) (3161389 / 62500000000) (50598023 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1648599677 / 500000000) (824325861 / 250000000) (927815573 / 500000000) (1855667363 / 1000000000) (3161389 / 62500000000) (50598023 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0299 :
    ∀ t ∈ Set.Icc ((387 / 16000) : ℝ) (1549 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1049564168099 / 1000000000000) : ℝ) ≤ Real.exp (2 * (387 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (387 / 16000)) (1049564168099 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1549 / 64000) : ℝ)) ≤ (262399241873 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1549 / 64000)) (262399241873 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1855666997 / 1000000000) : ℝ) ≤ Real.exp (3 * (3297302393 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3297302393 / 1000000000) / 16) (1855666997 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1648703243 / 500000000) : ℝ) / 16) ≤ (115981451 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1648703243 / 500000000) / 16) (115981451 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((387 / 16000) : ℝ) (1549 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3297302393 / 1000000000) (1648703243 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (387 / 16000) (1549 / 64000) (1049564168099 / 1000000000000) (262399241873 / 250000000000) (3297302393 / 1000000000) (1648703243 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (387 / 16000) (1549 / 64000) (3297302393 / 1000000000) (1648703243 / 500000000) (5056659 / 100000000000) (10116477 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3297302393 / 1000000000) (1648703243 / 500000000) (1855666997 / 1000000000) (115981451 / 62500000) (5056659 / 100000000000) (10116477 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch014 :
    ∀ t ∈ Set.Icc ((1529 / 64000) : ℝ) (1549 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0280
      hpThetaDensityTwoTermCompact_cell0281)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0282
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0283
      hpThetaDensityTwoTermCompact_cell0284)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0285
      hpThetaDensityTwoTermCompact_cell0286)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0287
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0288
      hpThetaDensityTwoTermCompact_cell0289))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0290
      hpThetaDensityTwoTermCompact_cell0291)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0292
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0293
      hpThetaDensityTwoTermCompact_cell0294)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0295
      hpThetaDensityTwoTermCompact_cell0296)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0297
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0298
      hpThetaDensityTwoTermCompact_cell0299)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch014
end HodgeProofHP
