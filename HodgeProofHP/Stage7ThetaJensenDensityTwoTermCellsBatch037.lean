/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0740 :
    ∀ t ∈ Set.Icc ((2543 / 64000) : ℝ) (2547 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1082711724259 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2543 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2543 / 64000)) (1082711724259 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2547 / 64000) : ℝ)) ≤ (270711767921 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2547 / 64000)) (270711767921 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1892255903 / 1000000000) : ℝ) ≤ Real.exp (3 * (3401438491 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3401438491 / 1000000000) / 16) (1892255903 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3401864781 / 1000000000) : ℝ) / 16) ≤ (1892407157 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3401864781 / 1000000000) / 16) (1892407157 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2543 / 64000) : ℝ) (2547 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3401438491 / 1000000000) (3401864781 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2543 / 64000) (2547 / 64000) (1082711724259 / 1000000000000) (270711767921 / 250000000000) (3401438491 / 1000000000) (3401864781 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2543 / 64000) (2547 / 64000) (3401438491 / 1000000000) (3401864781 / 1000000000) (7392591 / 200000000000) (37010257 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3401438491 / 1000000000) (3401864781 / 1000000000) (1892255903 / 1000000000) (1892407157 / 1000000000) (7392591 / 200000000000) (37010257 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0741 :
    ∀ t ∈ Set.Icc ((2547 / 64000) : ℝ) (2551 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1082847071683 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2547 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2547 / 64000)) (1082847071683 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2551 / 64000) : ℝ)) ≤ (1082982436029 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2551 / 64000)) (1082982436029 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1892406771 / 1000000000) : ℝ) ≤ Real.exp (3 * (3401863697 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3401863697 / 1000000000) / 16) (1892406771 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3402290041 / 1000000000) : ℝ) / 16) ≤ (236569757 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3402290041 / 1000000000) / 16) (236569757 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2547 / 64000) : ℝ) (2551 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3401863697 / 1000000000) (3402290041 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2547 / 64000) (2551 / 64000) (1082847071683 / 1000000000000) (1082982436029 / 1000000000000) (3401863697 / 1000000000) (3402290041 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2547 / 64000) (2551 / 64000) (3401863697 / 1000000000) (3402290041 / 1000000000) (36915829 / 1000000000000) (36963077 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3401863697 / 1000000000) (3402290041 / 1000000000) (1892406771 / 1000000000) (236569757 / 125000000) (36915829 / 1000000000000) (36963077 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0742 :
    ∀ t ∈ Set.Icc ((2551 / 64000) : ℝ) (511 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((270745609007 / 250000000000) : ℝ) ≤ Real.exp (2 * (2551 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2551 / 64000)) (270745609007 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((511 / 12800) : ℝ)) ≤ (541558908647 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (511 / 12800)) (541558908647 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1892557671 / 1000000000) : ℝ) ≤ Real.exp (3 * (3402288957 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3402288957 / 1000000000) / 16) (1892557671 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3402715353 / 1000000000) : ℝ) / 16) ≤ (946354493 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3402715353 / 1000000000) / 16) (946354493 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2551 / 64000) : ℝ) (511 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3402288957 / 1000000000) (3402715353 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2551 / 64000) (511 / 12800) (270745609007 / 250000000000) (541558908647 / 500000000000) (3402288957 / 1000000000) (3402715353 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2551 / 64000) (511 / 12800) (3402288957 / 1000000000) (3402715353 / 1000000000) (9217189 / 250000000000) (738319 / 20000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3402288957 / 1000000000) (3402715353 / 1000000000) (1892557671 / 1000000000) (946354493 / 500000000) (9217189 / 250000000000) (738319 / 20000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0743 :
    ∀ t ∈ Set.Icc ((511 / 12800) : ℝ) (2559 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1083117817293 / 1000000000000) : ℝ) ≤ Real.exp (2 * (511 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (511 / 12800)) (1083117817293 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2559 / 64000) : ℝ)) ≤ (270813303871 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2559 / 64000)) (270813303871 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1892708601 / 1000000000) : ℝ) ≤ Real.exp (3 * (3402714269 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3402714269 / 1000000000) / 16) (1892708601 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3403140719 / 1000000000) : ℝ) / 16) ≤ (473214987 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3403140719 / 1000000000) / 16) (473214987 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((511 / 12800) : ℝ) (2559 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3402714269 / 1000000000) (3403140719 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (511 / 12800) (2559 / 64000) (1083117817293 / 1000000000000) (270813303871 / 250000000000) (3402714269 / 1000000000) (3403140719 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (511 / 12800) (2559 / 64000) (3402714269 / 1000000000) (3403140719 / 1000000000) (18410869 / 500000000000) (36868877 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3402714269 / 1000000000) (3403140719 / 1000000000) (1892708601 / 1000000000) (473214987 / 250000000) (18410869 / 500000000000) (36868877 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0744 :
    ∀ t ∈ Set.Icc ((2559 / 64000) : ℝ) (2563 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1083253215483 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2559 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2559 / 64000)) (1083253215483 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2563 / 64000) : ℝ)) ≤ (1083388630599 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2563 / 64000)) (1083388630599 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((946429781 / 500000000) : ℝ) ≤ Real.exp (3 * (680627927 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (680627927 / 200000000) / 16) (946429781 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3403566139 / 1000000000) : ℝ) / 16) ≤ (94650547 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3403566139 / 1000000000) / 16) (94650547 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2559 / 64000) : ℝ) (2563 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (680627927 / 200000000) (3403566139 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2559 / 64000) (2563 / 64000) (1083253215483 / 1000000000000) (1083388630599 / 1000000000000) (680627927 / 200000000) (3403566139 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2559 / 64000) (2563 / 64000) (680627927 / 200000000) (3403566139 / 1000000000) (18387387 / 500000000000) (36821859 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (680627927 / 200000000) (3403566139 / 1000000000) (946429781 / 500000000) (94650547 / 50000000) (18387387 / 500000000000) (36821859 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0745 :
    ∀ t ∈ Set.Icc ((2563 / 64000) : ℝ) (2567 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((541694315299 / 500000000000) : ℝ) ≤ Real.exp (2 * (2563 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2563 / 64000)) (541694315299 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2567 / 64000) : ℝ)) ≤ (541762031321 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2567 / 64000)) (541762031321 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((946505277 / 500000000) : ℝ) ≤ Real.exp (3 * (1701782527 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1701782527 / 500000000) / 16) (946505277 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3403991611 / 1000000000) : ℝ) / 16) ≤ (1893161963 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3403991611 / 1000000000) / 16) (1893161963 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2563 / 64000) : ℝ) (2567 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1701782527 / 500000000) (3403991611 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2563 / 64000) (2567 / 64000) (541694315299 / 500000000000) (541762031321 / 500000000000) (1701782527 / 500000000) (3403991611 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2563 / 64000) (2567 / 64000) (1701782527 / 500000000) (3403991611 / 1000000000) (4590983 / 125000000000) (7354979 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1701782527 / 500000000) (3403991611 / 1000000000) (946505277 / 500000000) (1893161963 / 1000000000) (4590983 / 125000000000) (7354979 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0746 :
    ∀ t ∈ Set.Icc ((2567 / 64000) : ℝ) (2571 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1083524062641 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2567 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2567 / 64000)) (1083524062641 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2571 / 64000) : ℝ)) ≤ (216731902323 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2571 / 64000)) (216731902323 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1893161577 / 1000000000) : ℝ) ≤ Real.exp (3 * (3403990527 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3403990527 / 1000000000) / 16) (1893161577 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3404417137 / 1000000000) : ℝ) / 16) ≤ (1893313017 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3404417137 / 1000000000) / 16) (1893313017 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2567 / 64000) : ℝ) (2571 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3403990527 / 1000000000) (3404417137 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2567 / 64000) (2571 / 64000) (1083524062641 / 1000000000000) (216731902323 / 200000000000) (3403990527 / 1000000000) (3404417137 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2567 / 64000) (2571 / 64000) (3403990527 / 1000000000) (3404417137 / 1000000000) (2292563 / 62500000000) (7345597 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3403990527 / 1000000000) (3404417137 / 1000000000) (1893161577 / 1000000000) (1893313017 / 1000000000) (2292563 / 62500000000) (7345597 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0747 :
    ∀ t ∈ Set.Icc ((2571 / 64000) : ℝ) (103 / 2560), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((541829755807 / 500000000000) : ℝ) ≤ Real.exp (2 * (2571 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2571 / 64000)) (541829755807 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((103 / 2560) : ℝ)) ≤ (1083794977521 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (103 / 2560)) (1083794977521 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1893312631 / 1000000000) : ℝ) ≤ Real.exp (3 * (851104013 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (851104013 / 250000000) / 16) (1893312631 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((680968543 / 200000000) : ℝ) / 16) ≤ (1893464101 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (680968543 / 200000000) / 16) (1893464101 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2571 / 64000) : ℝ) (103 / 2560),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (851104013 / 250000000) (680968543 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2571 / 64000) (103 / 2560) (541829755807 / 500000000000) (1083794977521 / 1000000000000) (851104013 / 250000000) (680968543 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2571 / 64000) (103 / 2560) (851104013 / 250000000) (680968543 / 200000000) (18317103 / 500000000000) (36681129 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (851104013 / 250000000) (680968543 / 200000000) (1893312631 / 1000000000) (1893464101 / 1000000000) (18317103 / 500000000000) (36681129 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0748 :
    ∀ t ∈ Set.Icc ((103 / 2560) : ℝ) (2579 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((13547437219 / 12500000000) : ℝ) ≤ Real.exp (2 * (103 / 2560)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (103 / 2560)) (13547437219 / 12500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2579 / 64000) : ℝ)) ≤ (27098261509 / 25000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2579 / 64000)) (27098261509 / 25000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((473365929 / 250000000) : ℝ) ≤ Real.exp (3 * (3404841631 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3404841631 / 1000000000) / 16) (473365929 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3405268347 / 1000000000) : ℝ) / 16) ≤ (1893615217 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3405268347 / 1000000000) / 16) (1893615217 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((103 / 2560) : ℝ) (2579 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3404841631 / 1000000000) (3405268347 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (103 / 2560) (2579 / 64000) (13547437219 / 12500000000) (27098261509 / 25000000000) (3404841631 / 1000000000) (3405268347 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (103 / 2560) (2579 / 64000) (3404841631 / 1000000000) (3405268347 / 1000000000) (18293729 / 500000000000) (18317163 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3404841631 / 1000000000) (3405268347 / 1000000000) (473365929 / 250000000) (1893615217 / 1000000000) (18293729 / 500000000000) (18317163 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0749 :
    ∀ t ∈ Set.Icc ((2579 / 64000) : ℝ) (2583 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1083930460359 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2579 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2579 / 64000)) (1083930460359 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2583 / 64000) : ℝ)) ≤ (135508245017 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2583 / 64000)) (135508245017 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1893614831 / 1000000000) : ℝ) ≤ Real.exp (3 * (1702633631 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1702633631 / 500000000) / 16) (1893614831 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((212855877 / 62500000) : ℝ) / 16) ≤ (473441591 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (212855877 / 62500000) / 16) (473441591 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2579 / 64000) : ℝ) (2583 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1702633631 / 500000000) (212855877 / 62500000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2579 / 64000) (2583 / 64000) (1083930460359 / 1000000000000) (135508245017 / 125000000000) (1702633631 / 500000000) (212855877 / 62500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2579 / 64000) (2583 / 64000) (1702633631 / 500000000) (212855877 / 62500000) (36540763 / 1000000000000) (18293789 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1702633631 / 500000000) (212855877 / 62500000) (1893614831 / 1000000000) (473441591 / 250000000) (36540763 / 1000000000000) (18293789 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0750 :
    ∀ t ∈ Set.Icc ((2583 / 64000) : ℝ) (2587 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((216813192027 / 200000000000) : ℝ) ≤ Real.exp (2 * (2583 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2583 / 64000)) (216813192027 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2587 / 64000) : ℝ)) ≤ (1084201476851 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2587 / 64000)) (1084201476851 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((946882989 / 500000000) : ℝ) ≤ Real.exp (3 * (3405692947 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3405692947 / 1000000000) / 16) (946882989 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3406119771 / 1000000000) : ℝ) / 16) ≤ (946958771 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3406119771 / 1000000000) / 16) (946958771 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2583 / 64000) : ℝ) (2587 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3405692947 / 1000000000) (3406119771 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2583 / 64000) (2587 / 64000) (216813192027 / 200000000000) (1084201476851 / 1000000000000) (3405692947 / 1000000000) (3406119771 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2583 / 64000) (2587 / 64000) (3405692947 / 1000000000) (3406119771 / 1000000000) (36494123 / 1000000000000) (9135221 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3405692947 / 1000000000) (3406119771 / 1000000000) (946882989 / 500000000) (946958771 / 500000000) (36494123 / 1000000000000) (9135221 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0751 :
    ∀ t ∈ Set.Icc ((2587 / 64000) : ℝ) (2591 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((21684029537 / 20000000000) : ℝ) ≤ Real.exp (2 * (2587 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2587 / 64000)) (21684029537 / 20000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2591 / 64000) : ℝ)) ≤ (542168505253 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2591 / 64000)) (542168505253 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((473479289 / 250000000) : ℝ) ≤ Real.exp (3 * (1703059343 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1703059343 / 500000000) / 16) (473479289 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1703272781 / 500000000) : ℝ) / 16) ≤ (303051 / 160000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1703272781 / 500000000) / 16) (303051 / 160000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2587 / 64000) : ℝ) (2591 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1703059343 / 500000000) (1703272781 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2587 / 64000) (2591 / 64000) (21684029537 / 20000000000) (542168505253 / 500000000000) (1703059343 / 500000000) (1703272781 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2587 / 64000) (2591 / 64000) (1703059343 / 500000000) (1703272781 / 500000000) (2277971 / 62500000000) (36494243 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1703059343 / 500000000) (1703272781 / 500000000) (473479289 / 250000000) (303051 / 160000) (2277971 / 62500000000) (36494243 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0752 :
    ∀ t ∈ Set.Icc ((2591 / 64000) : ℝ) (519 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((216867402101 / 200000000000) : ℝ) ≤ Real.exp (2 * (2591 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2591 / 64000)) (216867402101 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((519 / 12800) : ℝ)) ≤ (67779535069 / 62500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (519 / 12800)) (67779535069 / 62500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((473517091 / 250000000) : ℝ) ≤ Real.exp (3 * (3406544477 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3406544477 / 1000000000) / 16) (473517091 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3406971407 / 1000000000) : ℝ) / 16) ≤ (189421999 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3406971407 / 1000000000) / 16) (189421999 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2591 / 64000) : ℝ) (519 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3406544477 / 1000000000) (3406971407 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2591 / 64000) (519 / 12800) (216867402101 / 200000000000) (67779535069 / 62500000000) (3406544477 / 1000000000) (3406971407 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2591 / 64000) (519 / 12800) (3406544477 / 1000000000) (3406971407 / 1000000000) (36401003 / 1000000000000) (4555957 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3406544477 / 1000000000) (3406971407 / 1000000000) (473517091 / 250000000) (189421999 / 100000000) (36401003 / 1000000000000) (4555957 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0753 :
    ∀ t ∈ Set.Icc ((519 / 12800) : ℝ) (2599 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1084472561103 / 1000000000000) : ℝ) ≤ Real.exp (2 * (519 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (519 / 12800)) (1084472561103 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2599 / 64000) : ℝ)) ≤ (1084608128647 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2599 / 64000)) (1084608128647 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((473554901 / 250000000) : ℝ) ≤ Real.exp (3 * (1703485161 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1703485161 / 500000000) / 16) (473554901 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((681479461 / 200000000) : ℝ) / 16) ≤ (1894371261 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (681479461 / 200000000) / 16) (1894371261 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((519 / 12800) : ℝ) (2599 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1703485161 / 500000000) (681479461 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (519 / 12800) (2599 / 64000) (1084472561103 / 1000000000000) (1084608128647 / 1000000000000) (1703485161 / 500000000) (681479461 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (519 / 12800) (2599 / 64000) (1703485161 / 500000000) (681479461 / 200000000) (36354523 / 1000000000000) (18200561 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1703485161 / 500000000) (681479461 / 200000000) (473554901 / 250000000) (1894371261 / 1000000000) (36354523 / 1000000000000) (18200561 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0754 :
    ∀ t ∈ Set.Icc ((2599 / 64000) : ℝ) (2603 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((542304064323 / 500000000000) : ℝ) ≤ Real.exp (2 * (2599 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2599 / 64000)) (542304064323 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2603 / 64000) : ℝ)) ≤ (1084743713137 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2603 / 64000)) (1084743713137 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((947185437 / 500000000) : ℝ) ≤ Real.exp (3 * (170369811 / 50000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (170369811 / 50000000) / 16) (947185437 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((425977907 / 125000000) : ℝ) / 16) ≤ (947261281 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (425977907 / 125000000) / 16) (947261281 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2599 / 64000) : ℝ) (2603 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (170369811 / 50000000) (425977907 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2599 / 64000) (2603 / 64000) (542304064323 / 500000000000) (1084743713137 / 1000000000000) (170369811 / 50000000) (425977907 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2599 / 64000) (2603 / 64000) (170369811 / 50000000) (425977907 / 125000000) (36308097 / 1000000000000) (36354643 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (170369811 / 50000000) (425977907 / 125000000) (947185437 / 500000000) (947261281 / 500000000) (36308097 / 1000000000000) (36354643 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0755 :
    ∀ t ∈ Set.Icc ((2603 / 64000) : ℝ) (2607 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((67796482071 / 62500000000) : ℝ) ≤ Real.exp (2 * (2603 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2603 / 64000)) (67796482071 / 62500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2607 / 64000) : ℝ)) ≤ (67804957161 / 62500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2607 / 64000)) (67804957161 / 62500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((29601909 / 15625000) : ℝ) ≤ Real.exp (3 * (3407822171 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3407822171 / 1000000000) / 16) (29601909 / 15625000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3408249261 / 1000000000) : ℝ) / 16) ≤ (378934779 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3408249261 / 1000000000) / 16) (378934779 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2603 / 64000) : ℝ) (2607 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3407822171 / 1000000000) (3408249261 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2603 / 64000) (2607 / 64000) (67796482071 / 62500000000) (67804957161 / 62500000000) (3407822171 / 1000000000) (3408249261 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2603 / 64000) (2607 / 64000) (3407822171 / 1000000000) (3408249261 / 1000000000) (9065431 / 250000000000) (4538527 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3407822171 / 1000000000) (3408249261 / 1000000000) (29601909 / 15625000) (378934779 / 200000000) (9065431 / 250000000000) (4538527 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0756 :
    ∀ t ∈ Set.Icc ((2607 / 64000) : ℝ) (2611 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((43395172583 / 40000000000) : ℝ) ≤ Real.exp (2 * (2607 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2607 / 64000)) (43395172583 / 40000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2611 / 64000) : ℝ)) ≤ (542507466483 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2611 / 64000)) (542507466483 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((473668377 / 250000000) : ℝ) ≤ Real.exp (3 * (136329927 / 40000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (136329927 / 40000000) / 16) (473668377 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3408675319 / 1000000000) : ℝ) / 16) ≤ (1894825259 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3408675319 / 1000000000) / 16) (1894825259 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2607 / 64000) : ℝ) (2611 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (136329927 / 40000000) (3408675319 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2607 / 64000) (2611 / 64000) (43395172583 / 40000000000) (542507466483 / 500000000000) (136329927 / 40000000) (3408675319 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2607 / 64000) (2611 / 64000) (136329927 / 40000000) (3408675319 / 1000000000) (7243081 / 200000000000) (9065461 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (136329927 / 40000000) (3408675319 / 1000000000) (473668377 / 250000000) (1894825259 / 1000000000) (7243081 / 200000000000) (9065461 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0757 :
    ∀ t ∈ Set.Icc ((2611 / 64000) : ℝ) (523 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((217002986593 / 200000000000) : ℝ) ≤ Real.exp (2 * (2611 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2611 / 64000)) (217002986593 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((523 / 12800) : ℝ)) ≤ (108515056831 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (523 / 12800)) (108515056831 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((236853109 / 125000000) : ℝ) ≤ Real.exp (3 * (3408674233 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3408674233 / 1000000000) / 16) (236853109 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((340910143 / 100000000) : ℝ) / 16) ≤ (1894976653 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (340910143 / 100000000) / 16) (1894976653 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2611 / 64000) : ℝ) (523 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3408674233 / 1000000000) (340910143 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2611 / 64000) (523 / 12800) (217002986593 / 200000000000) (108515056831 / 100000000000) (3408674233 / 1000000000) (340910143 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2611 / 64000) (523 / 12800) (3408674233 / 1000000000) (340910143 / 100000000) (36169139 / 1000000000000) (9053881 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3408674233 / 1000000000) (340910143 / 100000000) (236853109 / 125000000) (1894976653 / 1000000000) (36169139 / 1000000000000) (9053881 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0758 :
    ∀ t ∈ Set.Icc ((523 / 12800) : ℝ) (2619 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1085150568309 / 1000000000000) : ℝ) ≤ Real.exp (2 * (523 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (523 / 12800)) (1085150568309 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2619 / 64000) : ℝ)) ≤ (1085286220609 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2619 / 64000)) (1085286220609 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1894976267 / 1000000000) : ℝ) ≤ Real.exp (3 * (426137543 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (426137543 / 125000000) / 16) (1894976267 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1704763797 / 500000000) : ℝ) / 16) ≤ (1895128079 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1704763797 / 500000000) / 16) (1895128079 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((523 / 12800) : ℝ) (2619 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (426137543 / 125000000) (1704763797 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (523 / 12800) (2619 / 64000) (1085150568309 / 1000000000000) (1085286220609 / 1000000000000) (426137543 / 125000000) (1704763797 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (523 / 12800) (2619 / 64000) (426137543 / 125000000) (1704763797 / 500000000) (36122927 / 1000000000000) (18084629 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (426137543 / 125000000) (1704763797 / 500000000) (1894976267 / 1000000000) (1895128079 / 1000000000) (36122927 / 1000000000000) (18084629 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0759 :
    ∀ t ∈ Set.Icc ((2619 / 64000) : ℝ) (2623 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((16957597197 / 15625000000) : ℝ) ≤ Real.exp (2 * (2619 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2619 / 64000)) (16957597197 / 15625000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2623 / 64000) : ℝ)) ≤ (542710944933 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2623 / 64000)) (542710944933 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((473781923 / 250000000) : ℝ) ≤ Real.exp (3 * (852381627 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (852381627 / 250000000) / 16) (473781923 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((852488453 / 250000000) : ℝ) / 16) ≤ (118454971 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (852488453 / 250000000) / 16) (118454971 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2619 / 64000) : ℝ) (2623 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (852381627 / 250000000) (852488453 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2619 / 64000) (2623 / 64000) (16957597197 / 15625000000) (542710944933 / 500000000000) (852381627 / 250000000) (852488453 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2619 / 64000) (2623 / 64000) (852381627 / 250000000) (852488453 / 250000000) (1127399 / 31250000000) (18061523 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (852381627 / 250000000) (852488453 / 250000000) (473781923 / 250000000) (118454971 / 62500000) (1127399 / 31250000000) (18061523 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch037 :
    ∀ t ∈ Set.Icc ((2543 / 64000) : ℝ) (2623 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0740
      hpThetaDensityTwoTermCompact_cell0741)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0742
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0743
      hpThetaDensityTwoTermCompact_cell0744)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0745
      hpThetaDensityTwoTermCompact_cell0746)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0747
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0748
      hpThetaDensityTwoTermCompact_cell0749))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0750
      hpThetaDensityTwoTermCompact_cell0751)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0752
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0753
      hpThetaDensityTwoTermCompact_cell0754)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0755
      hpThetaDensityTwoTermCompact_cell0756)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0757
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0758
      hpThetaDensityTwoTermCompact_cell0759)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch037
end HodgeProofHP
