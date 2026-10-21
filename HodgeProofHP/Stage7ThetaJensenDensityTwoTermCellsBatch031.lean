/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0620 :
    ∀ t ∈ Set.Icc ((417 / 12800) : ℝ) (2087 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1067325781009 / 1000000000000) : ℝ) ≤ Real.exp (2 * (417 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (417 / 12800)) (1067325781009 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2087 / 64000) : ℝ)) ≤ (266848122739 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2087 / 64000)) (266848122739 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1875183741 / 1000000000) : ℝ) ≤ Real.exp (3 * (670620427 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (670620427 / 200000000) / 16) (1875183741 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1676656389 / 500000000) : ℝ) / 16) ≤ (375051561 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1676656389 / 500000000) / 16) (375051561 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((417 / 12800) : ℝ) (2087 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (670620427 / 200000000) (1676656389 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (417 / 12800) (2087 / 64000) (1067325781009 / 1000000000000) (266848122739 / 250000000000) (670620427 / 200000000) (1676656389 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (417 / 12800) (2087 / 64000) (670620427 / 200000000) (1676656389 / 500000000) (1068967 / 25000000000) (4278571 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (670620427 / 200000000) (1676656389 / 500000000) (1875183741 / 1000000000) (375051561 / 200000000) (1068967 / 25000000000) (4278571 / 100000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0621 :
    ∀ t ∈ Set.Icc ((2087 / 64000) : ℝ) (2089 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((213478498191 / 200000000000) : ℝ) ≤ Real.exp (2 * (2087 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2087 / 64000)) (213478498191 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2089 / 64000) : ℝ)) ≤ (1067459205071 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2089 / 64000)) (1067459205071 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1875257429 / 1000000000) : ℝ) ≤ Real.exp (3 * (335331171 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (335331171 / 100000000) / 16) (1875257429 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3353522367 / 1000000000) : ℝ) / 16) ≤ (1875331501 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3353522367 / 1000000000) / 16) (1875331501 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2087 / 64000) : ℝ) (2089 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (335331171 / 100000000) (3353522367 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2087 / 64000) (2089 / 64000) (213478498191 / 200000000000) (1067459205071 / 1000000000000) (335331171 / 100000000) (3353522367 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2087 / 64000) (2089 / 64000) (335331171 / 100000000) (3353522367 / 1000000000) (42731803 / 1000000000000) (21379409 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (335331171 / 100000000) (3353522367 / 1000000000) (1875257429 / 1000000000) (1875331501 / 1000000000) (42731803 / 1000000000000) (21379409 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0622 :
    ∀ t ∈ Set.Icc ((2089 / 64000) : ℝ) (2091 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((106745920507 / 100000000000) : ℝ) ≤ Real.exp (2 * (2089 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2089 / 64000)) (106745920507 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2091 / 64000) : ℝ)) ≤ (266881480839 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2091 / 64000)) (266881480839 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((468832781 / 250000000) : ℝ) ≤ Real.exp (3 * (1676760649 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1676760649 / 500000000) / 16) (468832781 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3353731969 / 1000000000) : ℝ) / 16) ≤ (1875405203 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3353731969 / 1000000000) / 16) (1875405203 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2089 / 64000) : ℝ) (2091 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1676760649 / 500000000) (3353731969 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2089 / 64000) (2091 / 64000) (106745920507 / 100000000000) (266881480839 / 250000000000) (1676760649 / 500000000) (3353731969 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2089 / 64000) (2091 / 64000) (1676760649 / 500000000) (3353731969 / 1000000000) (42704941 / 1000000000000) (42731941 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1676760649 / 500000000) (3353731969 / 1000000000) (468832781 / 250000000) (1875405203 / 1000000000) (42704941 / 1000000000000) (42731941 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0623 :
    ∀ t ∈ Set.Icc ((2091 / 64000) : ℝ) (2093 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((213505184671 / 200000000000) : ℝ) ≤ Real.exp (2 * (2091 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2091 / 64000)) (213505184671 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2093 / 64000) : ℝ)) ≤ (266898161453 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2093 / 64000)) (266898161453 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((937702413 / 500000000) : ℝ) ≤ Real.exp (3 * (33537309 / 10000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (33537309 / 10000000) / 16) (937702413 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3353941583 / 1000000000) : ℝ) / 16) ≤ (1875478913 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3353941583 / 1000000000) / 16) (1875478913 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2091 / 64000) : ℝ) (2093 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (33537309 / 10000000) (3353941583 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2091 / 64000) (2093 / 64000) (213505184671 / 200000000000) (266898161453 / 250000000000) (33537309 / 10000000) (3353941583 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2091 / 64000) (2093 / 64000) (33537309 / 10000000) (3353941583 / 1000000000) (8535619 / 200000000000) (1067627 / 25000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (33537309 / 10000000) (3353941583 / 1000000000) (937702413 / 500000000) (1875478913 / 1000000000) (8535619 / 200000000000) (1067627 / 25000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0624 :
    ∀ t ∈ Set.Icc ((2093 / 64000) : ℝ) (419 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1067592645811 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2093 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2093 / 64000)) (1067592645811 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((419 / 12800) : ℝ)) ≤ (1067659372437 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (419 / 12800)) (1067659372437 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((234434817 / 125000000) : ℝ) ≤ Real.exp (3 * (670788103 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (670788103 / 200000000) / 16) (234434817 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3354151211 / 1000000000) : ℝ) / 16) ≤ (1875552631 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3354151211 / 1000000000) / 16) (1875552631 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2093 / 64000) : ℝ) (419 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (670788103 / 200000000) (3354151211 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2093 / 64000) (419 / 12800) (1067592645811 / 1000000000000) (1067659372437 / 1000000000000) (670788103 / 200000000) (3354151211 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2093 / 64000) (419 / 12800) (670788103 / 200000000) (3354151211 / 1000000000) (333213 / 7812500000) (42678233 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (670788103 / 200000000) (3354151211 / 1000000000) (234434817 / 125000000) (1875552631 / 1000000000) (333213 / 7812500000) (42678233 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0625 :
    ∀ t ∈ Set.Icc ((419 / 12800) : ℝ) (2097 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((266914843109 / 250000000000) : ℝ) ≤ Real.exp (2 * (419 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (419 / 12800)) (266914843109 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2097 / 64000) : ℝ)) ≤ (1067726103233 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2097 / 64000)) (1067726103233 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((937776127 / 500000000) : ℝ) ≤ Real.exp (3 * (3354150143 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3354150143 / 1000000000) / 16) (937776127 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((838590213 / 250000000) : ℝ) / 16) ≤ (468906589 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (838590213 / 250000000) / 16) (468906589 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((419 / 12800) : ℝ) (2097 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3354150143 / 1000000000) (838590213 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (419 / 12800) (2097 / 64000) (266914843109 / 250000000000) (1067726103233 / 1000000000000) (3354150143 / 1000000000) (838590213 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (419 / 12800) (2097 / 64000) (3354150143 / 1000000000) (838590213 / 250000000) (666007 / 15625000000) (21325701 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3354150143 / 1000000000) (838590213 / 250000000) (937776127 / 500000000) (468906589 / 250000000) (666007 / 15625000000) (21325701 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0626 :
    ∀ t ∈ Set.Icc ((2097 / 64000) : ℝ) (2099 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((16683220363 / 15625000000) : ℝ) ≤ Real.exp (2 * (2097 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2097 / 64000)) (16683220363 / 15625000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2099 / 64000) : ℝ)) ≤ (5338964191 / 5000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2099 / 64000)) (5338964191 / 5000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1875625979 / 1000000000) : ℝ) ≤ Real.exp (3 * (419294973 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (419294973 / 125000000) / 16) (1875625979 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1677285253 / 500000000) : ℝ) / 16) ≤ (234462511 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1677285253 / 500000000) / 16) (234462511 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2097 / 64000) : ℝ) (2099 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (419294973 / 125000000) (1677285253 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2097 / 64000) (2099 / 64000) (16683220363 / 15625000000) (5338964191 / 5000000000) (419294973 / 125000000) (1677285253 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2097 / 64000) (2099 / 64000) (419294973 / 125000000) (1677285253 / 500000000) (42597647 / 1000000000000) (21312293 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (419294973 / 125000000) (1677285253 / 500000000) (1875625979 / 1000000000) (234462511 / 125000000) (42597647 / 1000000000000) (21312293 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0627 :
    ∀ t ∈ Set.Icc ((2099 / 64000) : ℝ) (2101 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1067792838199 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2099 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2099 / 64000)) (1067792838199 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2101 / 64000) : ℝ)) ≤ (533929788669 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2101 / 64000)) (533929788669 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((3663476 / 1953125) : ℝ) ≤ Real.exp (3 * (1677284719 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1677284719 / 500000000) / 16) (3663476 / 1953125) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1677390087 / 500000000) : ℝ) / 16) ≤ (1875773829 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1677390087 / 500000000) / 16) (1875773829 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2099 / 64000) : ℝ) (2101 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1677284719 / 500000000) (1677390087 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2099 / 64000) (2101 / 64000) (1067792838199 / 1000000000000) (533929788669 / 500000000000) (1677284719 / 500000000) (1677390087 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2099 / 64000) (2101 / 64000) (1677284719 / 500000000) (1677390087 / 500000000) (21285431 / 500000000000) (8519557 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1677284719 / 500000000) (1677390087 / 500000000) (3663476 / 1953125) (1875773829 / 1000000000) (21285431 / 500000000000) (8519557 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0628 :
    ∀ t ∈ Set.Icc ((2101 / 64000) : ℝ) (2103 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1067859577337 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2101 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2101 / 64000)) (1067859577337 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2103 / 64000) : ℝ)) ≤ (133490790081 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2103 / 64000)) (133490790081 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((468943363 / 250000000) : ℝ) ≤ Real.exp (3 * (670955821 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (670955821 / 200000000) / 16) (468943363 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1677494927 / 500000000) : ℝ) / 16) ≤ (234480947 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1677494927 / 500000000) / 16) (234480947 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2101 / 64000) : ℝ) (2103 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (670955821 / 200000000) (1677494927 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2101 / 64000) (2103 / 64000) (1067859577337 / 1000000000000) (133490790081 / 125000000000) (670955821 / 200000000) (1677494927 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2101 / 64000) (2103 / 64000) (670955821 / 200000000) (1677494927 / 500000000) (42544091 / 1000000000000) (42570999 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (670955821 / 200000000) (1677494927 / 500000000) (468943363 / 250000000) (234480947 / 125000000) (42544091 / 1000000000000) (42570999 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0629 :
    ∀ t ∈ Set.Icc ((2103 / 64000) : ℝ) (421 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1067926320647 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2103 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2103 / 64000)) (1067926320647 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((421 / 12800) : ℝ)) ≤ (33374783379 / 31250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (421 / 12800)) (33374783379 / 31250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1875847199 / 1000000000) : ℝ) ≤ Real.exp (3 * (670997757 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (670997757 / 200000000) / 16) (1875847199 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3355199547 / 1000000000) : ℝ) / 16) ≤ (1875921331 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3355199547 / 1000000000) / 16) (1875921331 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2103 / 64000) : ℝ) (421 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (670997757 / 200000000) (3355199547 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2103 / 64000) (421 / 12800) (1067926320647 / 1000000000000) (33374783379 / 31250000000) (670997757 / 200000000) (3355199547 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2103 / 64000) (421 / 12800) (670997757 / 200000000) (3355199547 / 1000000000) (5314667 / 125000000000) (42544229 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (670997757 / 200000000) (3355199547 / 1000000000) (1875847199 / 1000000000) (1875921331 / 1000000000) (5314667 / 125000000000) (42544229 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0630 :
    ∀ t ∈ Set.Icc ((421 / 12800) : ℝ) (2107 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1067993068127 / 1000000000000) : ℝ) ≤ Real.exp (2 * (421 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (421 / 12800)) (1067993068127 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2107 / 64000) : ℝ)) ≤ (1068059819781 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2107 / 64000)) (1068059819781 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((937960477 / 500000000) : ℝ) ≤ Real.exp (3 * (1677599239 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1677599239 / 500000000) / 16) (937960477 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1677704627 / 500000000) : ℝ) / 16) ≤ (937997547 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1677704627 / 500000000) / 16) (937997547 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((421 / 12800) : ℝ) (2107 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1677599239 / 500000000) (1677704627 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (421 / 12800) (2107 / 64000) (1067993068127 / 1000000000000) (1068059819781 / 1000000000000) (1677599239 / 500000000) (1677704627 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (421 / 12800) (2107 / 64000) (1677599239 / 500000000) (1677704627 / 500000000) (10622649 / 250000000000) (21258737 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1677599239 / 500000000) (1677704627 / 500000000) (937960477 / 500000000) (937997547 / 500000000) (10622649 / 250000000000) (21258737 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0631 :
    ∀ t ∈ Set.Icc ((2107 / 64000) : ℝ) (2111 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((53402990989 / 50000000000) : ℝ) ≤ Real.exp (2 * (2107 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2107 / 64000)) (53402990989 / 50000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2111 / 64000) : ℝ)) ≤ (1068193335603 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2111 / 64000)) (1068193335603 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1875994717 / 1000000000) : ℝ) ≤ Real.exp (3 * (671081637 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (671081637 / 200000000) / 16) (1875994717 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1677914353 / 500000000) : ℝ) / 16) ≤ (938071321 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1677914353 / 500000000) / 16) (938071321 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2107 / 64000) : ℝ) (2111 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (671081637 / 200000000) (1677914353 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2107 / 64000) (2111 / 64000) (53402990989 / 50000000000) (1068193335603 / 1000000000000) (671081637 / 200000000) (1677914353 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2107 / 64000) (2111 / 64000) (671081637 / 200000000) (1677914353 / 500000000) (42437161 / 1000000000000) (21245367 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (671081637 / 200000000) (1677914353 / 500000000) (1875994717 / 1000000000) (938071321 / 500000000) (42437161 / 1000000000000) (21245367 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0632 :
    ∀ t ∈ Set.Icc ((2111 / 64000) : ℝ) (423 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((534096667801 / 500000000000) : ℝ) ≤ Real.exp (2 * (2111 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2111 / 64000)) (534096667801 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((423 / 12800) : ℝ)) ≤ (267081717029 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (423 / 12800)) (267081717029 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((375228453 / 200000000) : ℝ) ≤ Real.exp (3 * (3355827637 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3355827637 / 1000000000) / 16) (375228453 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3356248211 / 1000000000) : ℝ) / 16) ≤ (1876290219 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3356248211 / 1000000000) / 16) (1876290219 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2111 / 64000) : ℝ) (423 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3355827637 / 1000000000) (3356248211 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2111 / 64000) (423 / 12800) (534096667801 / 500000000000) (267081717029 / 250000000000) (3355827637 / 1000000000) (3356248211 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2111 / 64000) (423 / 12800) (3355827637 / 1000000000) (3356248211 / 1000000000) (42383787 / 1000000000000) (42437299 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3355827637 / 1000000000) (3356248211 / 1000000000) (375228453 / 200000000) (1876290219 / 1000000000) (42383787 / 1000000000000) (42437299 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0633 :
    ∀ t ∈ Set.Icc ((423 / 12800) : ℝ) (2119 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((213665373623 / 200000000000) : ℝ) ≤ Real.exp (2 * (423 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (423 / 12800)) (213665373623 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2119 / 64000) : ℝ)) ≤ (1068460417321 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2119 / 64000)) (1068460417321 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((938144921 / 500000000) : ℝ) ≤ Real.exp (3 * (1678123571 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1678123571 / 500000000) / 16) (938144921 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((419583471 / 125000000) : ℝ) / 16) ≤ (1876437827 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (419583471 / 125000000) / 16) (1876437827 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((423 / 12800) : ℝ) (2119 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1678123571 / 500000000) (419583471 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (423 / 12800) (2119 / 64000) (213665373623 / 200000000000) (1068460417321 / 1000000000000) (1678123571 / 500000000) (419583471 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (423 / 12800) (2119 / 64000) (1678123571 / 500000000) (419583471 / 125000000) (42330473 / 1000000000000) (1695357 / 40000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1678123571 / 500000000) (419583471 / 125000000) (938144921 / 500000000) (1876437827 / 1000000000) (42330473 / 1000000000000) (1695357 / 40000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0634 :
    ∀ t ∈ Set.Icc ((2119 / 64000) : ℝ) (2123 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((26711510433 / 25000000000) : ℝ) ≤ Real.exp (2 * (2119 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2119 / 64000)) (26711510433 / 25000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2123 / 64000) : ℝ)) ≤ (1068593983221 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2123 / 64000)) (1068593983221 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((37528749 / 20000000) : ℝ) ≤ Real.exp (3 * (3356666699 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3356666699 / 1000000000) / 16) (37528749 / 20000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1678543689 / 500000000) : ℝ) / 16) ≤ (375317093 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1678543689 / 500000000) / 16) (375317093 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2119 / 64000) : ℝ) (2123 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3356666699 / 1000000000) (1678543689 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2119 / 64000) (2123 / 64000) (26711510433 / 25000000000) (1068593983221 / 1000000000000) (3356666699 / 1000000000) (1678543689 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2119 / 64000) (2123 / 64000) (3356666699 / 1000000000) (1678543689 / 500000000) (2113861 / 50000000000) (42330611 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3356666699 / 1000000000) (1678543689 / 500000000) (37528749 / 20000000) (375317093 / 200000000) (2113861 / 50000000000) (42330611 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0635 :
    ∀ t ∈ Set.Icc ((2123 / 64000) : ℝ) (2127 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((53429699161 / 50000000000) : ℝ) ≤ Real.exp (2 * (2123 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2123 / 64000)) (53429699161 / 50000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2127 / 64000) : ℝ)) ≤ (1068727565817 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2127 / 64000)) (1068727565817 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((14660821 / 7812500) : ℝ) ≤ Real.exp (3 * (839271577 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (839271577 / 250000000) / 16) (14660821 / 7812500) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((20984419 / 6250000) : ℝ) / 16) ≤ (1876733133 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (20984419 / 6250000) / 16) (1876733133 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2123 / 64000) : ℝ) (2127 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (839271577 / 250000000) (20984419 / 6250000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2123 / 64000) (2127 / 64000) (53429699161 / 50000000000) (1068727565817 / 1000000000000) (839271577 / 250000000) (20984419 / 6250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2123 / 64000) (2127 / 64000) (839271577 / 250000000) (20984419 / 6250000) (42224027 / 1000000000000) (42277357 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (839271577 / 250000000) (20984419 / 6250000) (14660821 / 7812500) (1876733133 / 1000000000) (42224027 / 1000000000000) (42277357 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0636 :
    ∀ t ∈ Set.Icc ((2127 / 64000) : ℝ) (2131 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((133590945727 / 125000000000) : ℝ) ≤ Real.exp (2 * (2127 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2127 / 64000)) (133590945727 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2131 / 64000) : ℝ)) ≤ (1068861165113 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2131 / 64000)) (1068861165113 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((469183189 / 250000000) : ℝ) ≤ Real.exp (3 * (335750597 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (335750597 / 100000000) / 16) (469183189 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((671585351 / 200000000) : ℝ) / 16) ≤ (29326263 / 15625000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (671585351 / 200000000) / 16) (29326263 / 15625000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2127 / 64000) : ℝ) (2131 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (335750597 / 100000000) (671585351 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2127 / 64000) (2131 / 64000) (133590945727 / 125000000000) (1068861165113 / 1000000000000) (335750597 / 100000000) (671585351 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2127 / 64000) (2131 / 64000) (335750597 / 100000000) (671585351 / 200000000) (21085447 / 500000000000) (10556041 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (335750597 / 100000000) (671585351 / 200000000) (469183189 / 250000000) (29326263 / 15625000) (21085447 / 500000000000) (10556041 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0637 :
    ∀ t ∈ Set.Icc ((2131 / 64000) : ℝ) (427 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((133607645639 / 125000000000) : ℝ) ≤ Real.exp (2 * (2131 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2131 / 64000)) (133607645639 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((427 / 12800) : ℝ)) ≤ (1068994781109 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (427 / 12800)) (1068994781109 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((938440227 / 500000000) : ℝ) ≤ Real.exp (3 * (671585137 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (671585137 / 200000000) / 16) (938440227 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1679173261 / 500000000) : ℝ) / 16) ≤ (23462857 / 12500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1679173261 / 500000000) / 16) (23462857 / 12500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2131 / 64000) : ℝ) (427 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (671585137 / 200000000) (1679173261 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2131 / 64000) (427 / 12800) (133607645639 / 125000000000) (1068994781109 / 1000000000000) (671585137 / 200000000) (1679173261 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2131 / 64000) (427 / 12800) (671585137 / 200000000) (1679173261 / 500000000) (21058911 / 500000000000) (42171031 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (671585137 / 200000000) (1679173261 / 500000000) (938440227 / 500000000) (23462857 / 12500000) (21058911 / 500000000000) (42171031 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0638 :
    ∀ t ∈ Set.Icc ((427 / 12800) : ℝ) (2139 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((267248695277 / 250000000000) : ℝ) ≤ Real.exp (2 * (427 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (427 / 12800)) (267248695277 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2139 / 64000) : ℝ)) ≤ (1069128413809 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2139 / 64000)) (1069128413809 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((938514091 / 500000000) : ℝ) ≤ Real.exp (3 * (839586363 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (839586363 / 250000000) / 16) (938514091 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3358766341 / 1000000000) : ℝ) / 16) ≤ (938588159 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3358766341 / 1000000000) / 16) (938588159 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((427 / 12800) : ℝ) (2139 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (839586363 / 250000000) (3358766341 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (427 / 12800) (2139 / 64000) (267248695277 / 250000000000) (1069128413809 / 1000000000000) (839586363 / 250000000) (3358766341 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (427 / 12800) (2139 / 64000) (839586363 / 250000000) (3358766341 / 1000000000) (4206481 / 100000000000) (42117959 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (839586363 / 250000000) (3358766341 / 1000000000) (938514091 / 500000000) (938588159 / 500000000) (4206481 / 100000000000) (42117959 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0639 :
    ∀ t ∈ Set.Icc ((2139 / 64000) : ℝ) (2143 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((66820525863 / 62500000000) : ℝ) ≤ Real.exp (2 * (2139 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2139 / 64000)) (66820525863 / 62500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2143 / 64000) : ℝ)) ≤ (534631031607 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2143 / 64000)) (534631031607 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((93858797 / 50000000) : ℝ) ≤ Real.exp (3 * (3358765271 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3358765271 / 1000000000) / 16) (93858797 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3359186213 / 1000000000) : ℝ) / 16) ≤ (938662053 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3359186213 / 1000000000) / 16) (938662053 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2139 / 64000) : ℝ) (2143 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3358765271 / 1000000000) (3359186213 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2139 / 64000) (2143 / 64000) (66820525863 / 62500000000) (534631031607 / 500000000000) (3358765271 / 1000000000) (3359186213 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2139 / 64000) (2143 / 64000) (3358765271 / 1000000000) (3359186213 / 1000000000) (21005929 / 500000000000) (21032473 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3358765271 / 1000000000) (3359186213 / 1000000000) (93858797 / 50000000) (938662053 / 500000000) (21005929 / 500000000000) (21032473 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch031 :
    ∀ t ∈ Set.Icc ((417 / 12800) : ℝ) (2143 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0620
      hpThetaDensityTwoTermCompact_cell0621)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0622
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0623
      hpThetaDensityTwoTermCompact_cell0624)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0625
      hpThetaDensityTwoTermCompact_cell0626)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0627
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0628
      hpThetaDensityTwoTermCompact_cell0629))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0630
      hpThetaDensityTwoTermCompact_cell0631)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0632
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0633
      hpThetaDensityTwoTermCompact_cell0634)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0635
      hpThetaDensityTwoTermCompact_cell0636)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0637
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0638
      hpThetaDensityTwoTermCompact_cell0639)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch031
end HodgeProofHP
