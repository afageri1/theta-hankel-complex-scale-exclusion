/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0760 :
    ∀ t ∈ Set.Icc ((2623 / 64000) : ℝ) (2627 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((217084377973 / 200000000000) : ℝ) ≤ Real.exp (2 * (2623 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2623 / 64000)) (217084377973 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2627 / 64000) : ℝ)) ≤ (542778788041 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2627 / 64000)) (542778788041 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1895279149 / 1000000000) : ℝ) ≤ Real.exp (3 * (136398109 / 40000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (136398109 / 40000000) / 16) (1895279149 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3410380083 / 1000000000) : ℝ) / 16) ≤ (118464439 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3410380083 / 1000000000) / 16) (118464439 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2623 / 64000) : ℝ) (2627 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (136398109 / 40000000) (3410380083 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2623 / 64000) (2627 / 64000) (217084377973 / 200000000000) (542778788041 / 500000000000) (136398109 / 40000000) (3410380083 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2623 / 64000) (2627 / 64000) (136398109 / 40000000) (3410380083 / 1000000000) (18015331 / 500000000000) (36076887 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (136398109 / 40000000) (3410380083 / 1000000000) (1895279149 / 1000000000) (118464439 / 62500000) (18015331 / 500000000000) (36076887 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0761 :
    ∀ t ∈ Set.Icc ((2627 / 64000) : ℝ) (2631 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1085557576081 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2627 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2627 / 64000)) (1085557576081 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2631 / 64000) : ℝ)) ≤ (1085693279261 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2631 / 64000)) (1085693279261 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((473857659 / 250000000) : ℝ) ≤ Real.exp (3 * (852594749 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (852594749 / 250000000) / 16) (473857659 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3410806407 / 1000000000) : ℝ) / 16) ≤ (947791271 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3410806407 / 1000000000) / 16) (947791271 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2627 / 64000) : ℝ) (2631 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (852594749 / 250000000) (3410806407 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2627 / 64000) (2631 / 64000) (1085557576081 / 1000000000000) (1085693279261 / 1000000000000) (852594749 / 250000000) (3410806407 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2627 / 64000) (2631 / 64000) (852594749 / 250000000) (3410806407 / 1000000000) (35984609 / 1000000000000) (36030781 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (852594749 / 250000000) (3410806407 / 1000000000) (473857659 / 250000000) (947791271 / 500000000) (35984609 / 1000000000000) (36030781 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0762 :
    ∀ t ∈ Set.Icc ((2631 / 64000) : ℝ) (527 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((54284663963 / 50000000000) : ℝ) ≤ Real.exp (2 * (2631 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2631 / 64000)) (54284663963 / 50000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((527 / 12800) : ℝ)) ≤ (1085828999403 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (527 / 12800)) (1085828999403 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((379116431 / 200000000) : ℝ) ≤ Real.exp (3 * (85270133 / 25000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (85270133 / 25000000) / 16) (379116431 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((213202049 / 62500000) : ℝ) / 16) ≤ (473933523 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (213202049 / 62500000) / 16) (473933523 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2631 / 64000) : ℝ) (527 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (85270133 / 25000000) (213202049 / 62500000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2631 / 64000) (527 / 12800) (54284663963 / 50000000000) (1085828999403 / 1000000000000) (85270133 / 25000000) (213202049 / 62500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2631 / 64000) (527 / 12800) (85270133 / 25000000) (213202049 / 62500000) (35938609 / 1000000000000) (4498091 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (85270133 / 25000000) (213202049 / 62500000) (379116431 / 200000000) (473933523 / 250000000) (35938609 / 1000000000000) (4498091 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0763 :
    ∀ t ∈ Set.Icc ((527 / 12800) : ℝ) (2639 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((542914499701 / 500000000000) : ℝ) ≤ Real.exp (2 * (527 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (527 / 12800)) (542914499701 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2639 / 64000) : ℝ)) ≤ (1085964736511 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2639 / 64000)) (1085964736511 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((379146741 / 200000000) : ℝ) ≤ Real.exp (3 * (3411231697 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3411231697 / 1000000000) / 16) (379146741 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((682331843 / 200000000) : ℝ) / 16) ≤ (1895885673 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (682331843 / 200000000) / 16) (1895885673 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((527 / 12800) : ℝ) (2639 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3411231697 / 1000000000) (682331843 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (527 / 12800) (2639 / 64000) (542914499701 / 500000000000) (1085964736511 / 1000000000000) (3411231697 / 1000000000) (682331843 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (527 / 12800) (2639 / 64000) (3411231697 / 1000000000) (682331843 / 200000000) (35892663 / 1000000000000) (4492341 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3411231697 / 1000000000) (682331843 / 200000000) (379146741 / 200000000) (1895885673 / 1000000000) (35892663 / 1000000000000) (4492341 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0764 :
    ∀ t ∈ Set.Icc ((2639 / 64000) : ℝ) (2643 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((108596473651 / 100000000000) : ℝ) ≤ Real.exp (2 * (2639 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2639 / 64000)) (108596473651 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2643 / 64000) : ℝ)) ≤ (271525122647 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2643 / 64000)) (271525122647 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((947942643 / 500000000) : ℝ) ≤ Real.exp (3 * (213228633 / 62500000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (213228633 / 62500000) / 16) (947942643 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3412085699 / 1000000000) : ℝ) / 16) ≤ (379207457 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3412085699 / 1000000000) / 16) (379207457 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2639 / 64000) : ℝ) (2643 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (213228633 / 62500000) (3412085699 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2639 / 64000) (2643 / 64000) (108596473651 / 100000000000) (271525122647 / 250000000000) (213228633 / 62500000) (3412085699 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2639 / 64000) (2643 / 64000) (213228633 / 62500000) (3412085699 / 1000000000) (35846769 / 1000000000000) (35892781 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (213228633 / 62500000) (3412085699 / 1000000000) (947942643 / 500000000) (379207457 / 200000000) (35846769 / 1000000000000) (35892781 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0765 :
    ∀ t ∈ Set.Icc ((2643 / 64000) : ℝ) (2647 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1086100490587 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2643 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2643 / 64000)) (1086100490587 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2647 / 64000) : ℝ)) ≤ (217247252327 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2647 / 64000)) (217247252327 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((948018449 / 500000000) : ℝ) ≤ Real.exp (3 * (853021153 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (853021153 / 250000000) / 16) (948018449 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((853128059 / 250000000) : ℝ) / 16) ≤ (3703494 / 1953125) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (853128059 / 250000000) / 16) (3703494 / 1953125) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2643 / 64000) : ℝ) (2647 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (853021153 / 250000000) (853128059 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2643 / 64000) (2647 / 64000) (1086100490587 / 1000000000000) (217247252327 / 200000000000) (853021153 / 250000000) (853128059 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2643 / 64000) (2647 / 64000) (853021153 / 250000000) (853128059 / 250000000) (35800929 / 1000000000000) (35846887 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (853021153 / 250000000) (853128059 / 250000000) (948018449 / 500000000) (3703494 / 1953125) (35800929 / 1000000000000) (35846887 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0766 :
    ∀ t ∈ Set.Icc ((2647 / 64000) : ℝ) (2651 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((543118130817 / 500000000000) : ℝ) ≤ Real.exp (2 * (2647 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2647 / 64000)) (543118130817 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2651 / 64000) : ℝ)) ≤ (543186024827 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2651 / 64000)) (543186024827 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1896188541 / 1000000000) : ℝ) ≤ Real.exp (3 * (3412511149 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3412511149 / 1000000000) / 16) (1896188541 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3412938827 / 1000000000) : ℝ) / 16) ≤ (948170301 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3412938827 / 1000000000) / 16) (948170301 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2647 / 64000) : ℝ) (2651 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3412511149 / 1000000000) (3412938827 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2647 / 64000) (2651 / 64000) (543118130817 / 500000000000) (543186024827 / 500000000000) (3412511149 / 1000000000) (3412938827 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2647 / 64000) (2651 / 64000) (3412511149 / 1000000000) (3412938827 / 1000000000) (35755141 / 1000000000000) (35801047 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3412511149 / 1000000000) (3412938827 / 1000000000) (1896188541 / 1000000000) (948170301 / 500000000) (35755141 / 1000000000000) (35801047 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0767 :
    ∀ t ∈ Set.Icc ((2651 / 64000) : ℝ) (531 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1086372049653 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2651 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2651 / 64000)) (1086372049653 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((531 / 12800) : ℝ)) ≤ (135813481831 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (531 / 12800)) (135813481831 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((379268043 / 200000000) : ℝ) ≤ Real.exp (3 * (170646887 / 50000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (170646887 / 50000000) / 16) (379268043 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3413365471 / 1000000000) : ℝ) / 16) ≤ (474123077 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3413365471 / 1000000000) / 16) (474123077 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2651 / 64000) : ℝ) (531 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (170646887 / 50000000) (3413365471 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2651 / 64000) (531 / 12800) (1086372049653 / 1000000000000) (135813481831 / 125000000000) (170646887 / 50000000) (3413365471 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2651 / 64000) (531 / 12800) (170646887 / 50000000) (3413365471 / 1000000000) (17854703 / 500000000000) (35755259 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (170646887 / 50000000) (3413365471 / 1000000000) (379268043 / 200000000) (474123077 / 250000000) (17854703 / 500000000000) (35755259 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0768 :
    ∀ t ∈ Set.Icc ((531 / 12800) : ℝ) (2659 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1086507854647 / 1000000000000) : ℝ) ≤ Real.exp (2 * (531 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (531 / 12800)) (1086507854647 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2659 / 64000) : ℝ)) ≤ (543321838309 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2659 / 64000)) (543321838309 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((23706149 / 12500000) : ℝ) ≤ Real.exp (3 * (106667637 / 31250000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (106667637 / 31250000) / 16) (23706149 / 12500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((426724021 / 125000000) : ℝ) / 16) ≤ (474161011 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (426724021 / 125000000) / 16) (474161011 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((531 / 12800) : ℝ) (2659 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (106667637 / 31250000) (426724021 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (531 / 12800) (2659 / 64000) (1086507854647 / 1000000000000) (543321838309 / 500000000000) (106667637 / 31250000) (426724021 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (531 / 12800) (2659 / 64000) (106667637 / 31250000) (426724021 / 125000000) (8915931 / 250000000000) (8927381 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (106667637 / 31250000) (426724021 / 125000000) (23706149 / 12500000) (474161011 / 250000000) (8915931 / 250000000000) (8927381 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0769 :
    ∀ t ∈ Set.Icc ((2659 / 64000) : ℝ) (2663 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1086643676617 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2659 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2659 / 64000)) (1086643676617 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2663 / 64000) : ℝ)) ≤ (67923719723 / 62500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2663 / 64000)) (67923719723 / 62500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((237080457 / 125000000) : ℝ) ≤ Real.exp (3 * (3413791081 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3413791081 / 1000000000) / 16) (237080457 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3414218919 / 1000000000) : ℝ) / 16) ≤ (474198953 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3414218919 / 1000000000) / 16) (474198953 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2659 / 64000) : ℝ) (2663 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3413791081 / 1000000000) (3414218919 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2659 / 64000) (2663 / 64000) (1086643676617 / 1000000000000) (67923719723 / 62500000000) (3413791081 / 1000000000) (3414218919 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2659 / 64000) (2663 / 64000) (3413791081 / 1000000000) (3414218919 / 1000000000) (17809047 / 500000000000) (17831921 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3413791081 / 1000000000) (3414218919 / 1000000000) (237080457 / 125000000) (474198953 / 250000000) (17809047 / 500000000000) (17831921 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0770 :
    ∀ t ∈ Set.Icc ((2663 / 64000) : ℝ) (2667 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1086779515567 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2663 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2663 / 64000)) (1086779515567 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2667 / 64000) : ℝ)) ≤ (543457685749 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2667 / 64000)) (543457685749 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((59274857 / 31250000) : ℝ) ≤ Real.exp (3 * (3414217831 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3414217831 / 1000000000) / 16) (59274857 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3414645723 / 1000000000) : ℝ) / 16) ≤ (189694761 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3414645723 / 1000000000) / 16) (189694761 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2663 / 64000) : ℝ) (2667 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3414217831 / 1000000000) (3414645723 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2663 / 64000) (2667 / 64000) (1086779515567 / 1000000000000) (543457685749 / 500000000000) (3414217831 / 1000000000) (3414645723 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2663 / 64000) (2667 / 64000) (3414217831 / 1000000000) (3414645723 / 1000000000) (17786259 / 500000000000) (8904553 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3414217831 / 1000000000) (3414645723 / 1000000000) (59274857 / 31250000) (189694761 / 100000000) (17786259 / 500000000000) (8904553 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0771 :
    ∀ t ∈ Set.Icc ((2667 / 64000) : ℝ) (2671 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1086915371497 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2667 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2667 / 64000)) (1086915371497 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2671 / 64000) : ℝ)) ≤ (1087051244411 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2671 / 64000)) (1087051244411 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((948473611 / 500000000) : ℝ) ≤ Real.exp (3 * (682928927 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (682928927 / 200000000) / 16) (948473611 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3415072581 / 1000000000) : ℝ) / 16) ≤ (23713743 / 12500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3415072581 / 1000000000) / 16) (23713743 / 12500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2667 / 64000) : ℝ) (2671 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (682928927 / 200000000) (3415072581 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2667 / 64000) (2671 / 64000) (1086915371497 / 1000000000000) (1087051244411 / 1000000000000) (682928927 / 200000000) (3415072581 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2667 / 64000) (2671 / 64000) (682928927 / 200000000) (3415072581 / 1000000000) (17763497 / 500000000000) (7114527 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (682928927 / 200000000) (3415072581 / 1000000000) (948473611 / 500000000) (23713743 / 12500000) (17763497 / 500000000000) (7114527 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0772 :
    ∀ t ∈ Set.Icc ((2671 / 64000) : ℝ) (107 / 2560), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((108705124441 / 100000000000) : ℝ) ≤ Real.exp (2 * (2671 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2671 / 64000)) (108705124441 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((107 / 2560) : ℝ)) ≤ (108718713431 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (107 / 2560)) (108718713431 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((474274763 / 250000000) : ℝ) ≤ Real.exp (3 * (3415071493 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3415071493 / 1000000000) / 16) (474274763 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3415499491 / 1000000000) : ℝ) / 16) ≤ (1897251301 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3415499491 / 1000000000) / 16) (1897251301 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2671 / 64000) : ℝ) (107 / 2560),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3415071493 / 1000000000) (3415499491 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2671 / 64000) (107 / 2560) (108705124441 / 100000000000) (108718713431 / 100000000000) (3415071493 / 1000000000) (3415499491 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2671 / 64000) (107 / 2560) (3415071493 / 1000000000) (3415499491 / 1000000000) (17740761 / 500000000000) (35527111 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3415071493 / 1000000000) (3415499491 / 1000000000) (474274763 / 250000000) (1897251301 / 1000000000) (17740761 / 500000000000) (35527111 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0773 :
    ∀ t ∈ Set.Icc ((107 / 2560) : ℝ) (2679 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1087187134309 / 1000000000000) : ℝ) ≤ Real.exp (2 * (107 / 2560)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (107 / 2560)) (1087187134309 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2679 / 64000) : ℝ)) ≤ (217464608239 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2679 / 64000)) (217464608239 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1897250913 / 1000000000) : ℝ) ≤ Real.exp (3 * (3415498403 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3415498403 / 1000000000) / 16) (1897250913 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((683185291 / 200000000) : ℝ) / 16) ≤ (1897403193 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (683185291 / 200000000) / 16) (1897403193 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((107 / 2560) : ℝ) (2679 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3415498403 / 1000000000) (683185291 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (107 / 2560) (2679 / 64000) (1087187134309 / 1000000000000) (217464608239 / 200000000000) (3415498403 / 1000000000) (683185291 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (107 / 2560) (2679 / 64000) (3415498403 / 1000000000) (683185291 / 200000000) (35436103 / 1000000000000) (35481639 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3415498403 / 1000000000) (683185291 / 200000000) (1897250913 / 1000000000) (1897403193 / 1000000000) (35436103 / 1000000000000) (35481639 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0774 :
    ∀ t ∈ Set.Icc ((2679 / 64000) : ℝ) (2683 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((543661520597 / 500000000000) : ℝ) ≤ Real.exp (2 * (2679 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2679 / 64000)) (543661520597 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2683 / 64000) : ℝ)) ≤ (1087458965071 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2683 / 64000)) (1087458965071 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((474350701 / 250000000) : ℝ) ≤ Real.exp (3 * (3415925367 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3415925367 / 1000000000) / 16) (474350701 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3416353473 / 1000000000) : ℝ) / 16) ≤ (474388779 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3416353473 / 1000000000) / 16) (474388779 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2679 / 64000) : ℝ) (2683 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3415925367 / 1000000000) (3416353473 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2679 / 64000) (2683 / 64000) (543661520597 / 500000000000) (1087458965071 / 1000000000000) (3415925367 / 1000000000) (3416353473 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2679 / 64000) (2683 / 64000) (3415925367 / 1000000000) (3416353473 / 1000000000) (35390737 / 1000000000000) (35436221 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3415925367 / 1000000000) (3416353473 / 1000000000) (474350701 / 250000000) (474388779 / 250000000) (35390737 / 1000000000000) (35436221 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0775 :
    ∀ t ∈ Set.Icc ((2683 / 64000) : ℝ) (2687 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((108745896507 / 100000000000) : ℝ) ≤ Real.exp (2 * (2683 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2683 / 64000)) (108745896507 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2687 / 64000) : ℝ)) ≤ (1087594905937 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2687 / 64000)) (1087594905937 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1897554727 / 1000000000) : ℝ) ≤ Real.exp (3 * (26690253 / 7812500) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (26690253 / 7812500) / 16) (1897554727 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((13346799 / 3906250) : ℝ) / 16) ≤ (189770707 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (13346799 / 3906250) / 16) (189770707 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2683 / 64000) : ℝ) (2687 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (26690253 / 7812500) (13346799 / 3906250) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2683 / 64000) (2687 / 64000) (108745896507 / 100000000000) (1087594905937 / 1000000000000) (26690253 / 7812500) (13346799 / 3906250) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2683 / 64000) (2687 / 64000) (26690253 / 7812500) (13346799 / 3906250) (35345423 / 1000000000000) (17695427 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (26690253 / 7812500) (13346799 / 3906250) (1897554727 / 1000000000) (189770707 / 100000000) (35345423 / 1000000000000) (17695427 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0776 :
    ∀ t ∈ Set.Icc ((2687 / 64000) : ℝ) (2691 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((67974681621 / 62500000000) : ℝ) ≤ Real.exp (2 * (2687 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2687 / 64000)) (67974681621 / 62500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2691 / 64000) : ℝ)) ≤ (543865431899 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2691 / 64000)) (543865431899 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((948853341 / 500000000) : ℝ) ≤ Real.exp (3 * (683355891 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (683355891 / 200000000) / 16) (948853341 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((854301917 / 250000000) : ℝ) / 16) ≤ (118616191 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (854301917 / 250000000) / 16) (118616191 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2687 / 64000) : ℝ) (2691 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (683355891 / 200000000) (854301917 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2687 / 64000) (2691 / 64000) (67974681621 / 62500000000) (543865431899 / 500000000000) (683355891 / 200000000) (854301917 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2687 / 64000) (2691 / 64000) (683355891 / 200000000) (854301917 / 250000000) (35300161 / 1000000000000) (1767277 / 50000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (683355891 / 200000000) (854301917 / 250000000) (948853341 / 500000000) (118616191 / 62500000) (35300161 / 1000000000000) (1767277 / 50000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0777 :
    ∀ t ∈ Set.Icc ((2691 / 64000) : ℝ) (539 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1087730863797 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2691 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2691 / 64000)) (1087730863797 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((539 / 12800) : ℝ)) ≤ (543933419327 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (539 / 12800)) (543933419327 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1897858667 / 1000000000) : ℝ) ≤ Real.exp (3 * (3417206579 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3417206579 / 1000000000) / 16) (1897858667 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1708817423 / 500000000) : ℝ) / 16) ≤ (29656423 / 15625000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1708817423 / 500000000) / 16) (29656423 / 15625000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2691 / 64000) : ℝ) (539 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3417206579 / 1000000000) (1708817423 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2691 / 64000) (539 / 12800) (1087730863797 / 1000000000000) (543933419327 / 500000000000) (3417206579 / 1000000000) (1708817423 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2691 / 64000) (539 / 12800) (3417206579 / 1000000000) (1708817423 / 500000000) (4406869 / 125000000000) (17650139 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3417206579 / 1000000000) (1708817423 / 500000000) (1897858667 / 1000000000) (29656423 / 15625000) (4406869 / 125000000000) (17650139 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0778 :
    ∀ t ∈ Set.Icc ((539 / 12800) : ℝ) (2699 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1087866838653 / 1000000000000) : ℝ) ≤ Real.exp (2 * (539 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (539 / 12800)) (1087866838653 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2699 / 64000) : ℝ)) ≤ (272000707627 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2699 / 64000)) (272000707627 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((474502671 / 250000000) : ℝ) ≤ Real.exp (3 * (3417633757 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3417633757 / 1000000000) / 16) (474502671 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3418062077 / 1000000000) : ℝ) / 16) ≤ (23727039 / 12500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3418062077 / 1000000000) / 16) (23727039 / 12500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((539 / 12800) : ℝ) (2699 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3417633757 / 1000000000) (3418062077 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (539 / 12800) (2699 / 64000) (1087866838653 / 1000000000000) (272000707627 / 250000000000) (3417633757 / 1000000000) (3418062077 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (539 / 12800) (2699 / 64000) (3417633757 / 1000000000) (3418062077 / 1000000000) (7041959 / 200000000000) (8813767 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3417633757 / 1000000000) (3418062077 / 1000000000) (474502671 / 250000000) (23727039 / 12500000) (7041959 / 200000000000) (8813767 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0779 :
    ∀ t ∈ Set.Icc ((2699 / 64000) : ℝ) (2703 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1088002830507 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2699 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2699 / 64000)) (1088002830507 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2703 / 64000) : ℝ)) ≤ (544069419681 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2703 / 64000)) (544069419681 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((474540683 / 250000000) : ℝ) ≤ Real.exp (3 * (854515247 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (854515247 / 250000000) / 16) (474540683 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3418489361 / 1000000000) : ℝ) / 16) ≤ (1898315199 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3418489361 / 1000000000) / 16) (1898315199 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2699 / 64000) : ℝ) (2703 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (854515247 / 250000000) (3418489361 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2699 / 64000) (2703 / 64000) (1088002830507 / 1000000000000) (544069419681 / 500000000000) (854515247 / 250000000) (3418489361 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2699 / 64000) (2703 / 64000) (854515247 / 250000000) (3418489361 / 1000000000) (3516469 / 100000000000) (35209911 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (854515247 / 250000000) (3418489361 / 1000000000) (474540683 / 250000000) (1898315199 / 1000000000) (3516469 / 100000000000) (35209911 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch038 :
    ∀ t ∈ Set.Icc ((2623 / 64000) : ℝ) (2703 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0760
      hpThetaDensityTwoTermCompact_cell0761)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0762
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0763
      hpThetaDensityTwoTermCompact_cell0764)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0765
      hpThetaDensityTwoTermCompact_cell0766)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0767
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0768
      hpThetaDensityTwoTermCompact_cell0769))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0770
      hpThetaDensityTwoTermCompact_cell0771)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0772
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0773
      hpThetaDensityTwoTermCompact_cell0774)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0775
      hpThetaDensityTwoTermCompact_cell0776)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0777
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0778
      hpThetaDensityTwoTermCompact_cell0779)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch038
end HodgeProofHP
