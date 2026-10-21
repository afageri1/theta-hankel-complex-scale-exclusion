/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0000 :
    ∀ t ∈ Set.Icc ((1 / 50) : ℝ) (2561 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((65050673387 / 62500000000) : ℝ) ≤ Real.exp (2 * (1 / 50)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1 / 50)) (65050673387 / 62500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2561 / 128000) : ℝ)) ≤ (260206759247 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2561 / 128000)) (260206759247 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1846123481 / 1000000000) : ℝ) ≤ Real.exp (3 * (3269802801 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3269802801 / 1000000000) / 16) (1846123481 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1634927467 / 500000000) : ℝ) / 16) ≤ (230767691 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1634927467 / 500000000) / 16) (230767691 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1 / 50) : ℝ) (2561 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3269802801 / 1000000000) (1634927467 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1 / 50) (2561 / 128000) (65050673387 / 62500000000) (260206759247 / 250000000000) (3269802801 / 1000000000) (1634927467 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1 / 50) (2561 / 128000) (3269802801 / 1000000000) (1634927467 / 500000000) (54923743 / 1000000000000) (3433271 / 62500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3269802801 / 1000000000) (1634927467 / 500000000) (1846123481 / 1000000000) (230767691 / 125000000) (54923743 / 1000000000000) (3433271 / 62500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0001 :
    ∀ t ∈ Set.Icc ((2561 / 128000) : ℝ) (1281 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1040827036987 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2561 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2561 / 128000)) (1040827036987 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1281 / 64000) : ℝ)) ≤ (520421650019 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1281 / 64000)) (520421650019 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((923070583 / 500000000) : ℝ) ≤ Real.exp (3 * (817463473 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (817463473 / 250000000) / 16) (923070583 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1634953013 / 500000000) : ℝ) / 16) ≤ (1846159213 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1634953013 / 500000000) / 16) (1846159213 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2561 / 128000) : ℝ) (1281 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (817463473 / 250000000) (1634953013 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2561 / 128000) (1281 / 64000) (1040827036987 / 1000000000000) (520421650019 / 500000000000) (817463473 / 250000000) (1634953013 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2561 / 128000) (1281 / 64000) (817463473 / 250000000) (1634953013 / 500000000) (27457663 / 500000000000) (54923917 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (817463473 / 250000000) (1634953013 / 500000000) (923070583 / 500000000) (1846159213 / 1000000000) (27457663 / 500000000000) (54923917 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0002 :
    ∀ t ∈ Set.Icc ((1281 / 64000) : ℝ) (2563 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1040843300037 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1281 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1281 / 64000)) (1040843300037 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2563 / 128000) : ℝ)) ≤ (1040859563341 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2563 / 128000)) (1040859563341 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((461539713 / 250000000) : ℝ) ≤ Real.exp (3 * (408738123 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (408738123 / 125000000) / 16) (461539713 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3269957119 / 1000000000) : ℝ) / 16) ≤ (18461769 / 10000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3269957119 / 1000000000) / 16) (18461769 / 10000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1281 / 64000) : ℝ) (2563 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (408738123 / 125000000) (3269957119 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1281 / 64000) (2563 / 128000) (1040843300037 / 1000000000000) (1040859563341 / 1000000000000) (408738123 / 125000000) (3269957119 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1281 / 64000) (2563 / 128000) (408738123 / 125000000) (3269957119 / 1000000000) (54906909 / 1000000000000) (54915499 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (408738123 / 125000000) (3269957119 / 1000000000) (461539713 / 250000000) (18461769 / 10000000) (54906909 / 1000000000000) (54915499 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0003 :
    ∀ t ∈ Set.Icc ((2563 / 128000) : ℝ) (641 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((52042978167 / 50000000000) : ℝ) ≤ Real.exp (2 * (2563 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2563 / 128000)) (52042978167 / 50000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((641 / 32000) : ℝ)) ≤ (1040875826899 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (641 / 32000)) (1040875826899 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((923088269 / 500000000) : ℝ) ≤ Real.exp (3 * (3269956077 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3269956077 / 1000000000) / 16) (923088269 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((817502053 / 250000000) : ℝ) / 16) ≤ (923097293 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (817502053 / 250000000) / 16) (923097293 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2563 / 128000) : ℝ) (641 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3269956077 / 1000000000) (817502053 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2563 / 128000) (641 / 32000) (52042978167 / 50000000000) (1040875826899 / 1000000000000) (3269956077 / 1000000000) (817502053 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2563 / 128000) (641 / 32000) (3269956077 / 1000000000) (817502053 / 250000000) (27449247 / 500000000000) (27453541 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3269956077 / 1000000000) (817502053 / 250000000) (923088269 / 500000000) (923097293 / 500000000) (27449247 / 500000000000) (27453541 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0004 :
    ∀ t ∈ Set.Icc ((641 / 32000) : ℝ) (513 / 25600), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((520437913449 / 500000000000) : ℝ) ≤ Real.exp (2 * (641 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (641 / 32000)) (520437913449 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((513 / 25600) : ℝ)) ≤ (1040892090711 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (513 / 25600)) (1040892090711 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((115387139 / 62500000) : ℝ) ≤ Real.exp (3 * (327000717 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (327000717 / 100000000) / 16) (115387139 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1635029653 / 500000000) : ℝ) / 16) ≤ (1846212273 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1635029653 / 500000000) / 16) (1846212273 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((641 / 32000) : ℝ) (513 / 25600),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (327000717 / 100000000) (1635029653 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (641 / 32000) (513 / 25600) (520437913449 / 500000000000) (1040892090711 / 1000000000000) (327000717 / 100000000) (1635029653 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (641 / 32000) (513 / 25600) (327000717 / 100000000) (1635029653 / 500000000) (54890079 / 1000000000000) (54898667 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (327000717 / 100000000) (1635029653 / 500000000) (115387139 / 62500000) (1846212273 / 1000000000) (54890079 / 1000000000000) (54898667 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0005 :
    ∀ t ∈ Set.Icc ((513 / 25600) : ℝ) (1283 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((104089209071 / 100000000000) : ℝ) ≤ Real.exp (2 * (513 / 25600)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (513 / 25600)) (104089209071 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1283 / 64000) : ℝ)) ≤ (1040908354777 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1283 / 64000)) (1040908354777 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1846211911 / 1000000000) : ℝ) ≤ Real.exp (3 * (654011653 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (654011653 / 200000000) / 16) (1846211911 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1635055201 / 500000000) : ℝ) / 16) ≤ (1846229961 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1635055201 / 500000000) / 16) (1846229961 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((513 / 25600) : ℝ) (1283 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (654011653 / 200000000) (1635055201 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (513 / 25600) (1283 / 64000) (104089209071 / 100000000000) (1040908354777 / 1000000000000) (654011653 / 200000000) (1635055201 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (513 / 25600) (1283 / 64000) (654011653 / 200000000) (1635055201 / 500000000) (27440833 / 500000000000) (13722563 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (654011653 / 200000000) (1635055201 / 500000000) (1846211911 / 1000000000) (1846229961 / 1000000000) (27440833 / 500000000000) (13722563 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0006 :
    ∀ t ∈ Set.Icc ((1283 / 64000) : ℝ) (2567 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((130113544347 / 125000000000) : ℝ) ≤ Real.exp (2 * (1283 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1283 / 64000)) (130113544347 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2567 / 128000) : ℝ)) ≤ (1040924619097 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2567 / 128000)) (1040924619097 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1846229599 / 1000000000) : ℝ) ≤ Real.exp (3 * (40876367 / 12500000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (40876367 / 12500000) / 16) (1846229599 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3270161497 / 1000000000) : ℝ) / 16) ≤ (57695239 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3270161497 / 1000000000) / 16) (57695239 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1283 / 64000) : ℝ) (2567 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (40876367 / 12500000) (3270161497 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1283 / 64000) (2567 / 128000) (130113544347 / 125000000000) (1040924619097 / 1000000000000) (40876367 / 12500000) (3270161497 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1283 / 64000) (2567 / 128000) (40876367 / 12500000) (3270161497 / 1000000000) (27436627 / 500000000000) (54881839 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (40876367 / 12500000) (3270161497 / 1000000000) (1846229599 / 1000000000) (57695239 / 31250000) (27436627 / 500000000000) (54881839 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0007 :
    ∀ t ∈ Set.Icc ((2567 / 128000) : ℝ) (321 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((130115577387 / 125000000000) : ℝ) ≤ Real.exp (2 * (2567 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2567 / 128000)) (130115577387 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((321 / 16000) : ℝ)) ≤ (1040940883671 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (321 / 16000)) (1040940883671 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((923123643 / 500000000) : ℝ) ≤ Real.exp (3 * (654032091 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (654032091 / 200000000) / 16) (923123643 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1635106297 / 500000000) : ℝ) / 16) ≤ (230783167 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1635106297 / 500000000) / 16) (230783167 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2567 / 128000) : ℝ) (321 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (654032091 / 200000000) (1635106297 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2567 / 128000) (321 / 16000) (130115577387 / 125000000000) (1040940883671 / 1000000000000) (654032091 / 200000000) (1635106297 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2567 / 128000) (321 / 16000) (654032091 / 200000000) (1635106297 / 500000000) (54864843 / 1000000000000) (54873427 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (654032091 / 200000000) (1635106297 / 500000000) (923123643 / 500000000) (230783167 / 125000000) (54864843 / 1000000000000) (54873427 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0008 :
    ∀ t ∈ Set.Icc ((321 / 16000) : ℝ) (2569 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((104094088367 / 100000000000) : ℝ) ≤ Real.exp (2 * (321 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (321 / 16000)) (104094088367 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2569 / 128000) : ℝ)) ≤ (2081914297 / 2000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2569 / 128000)) (2081914297 / 2000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((73850599 / 40000000) : ℝ) ≤ Real.exp (3 * (102194111 / 31250000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (102194111 / 31250000) / 16) (73850599 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((817565923 / 250000000) : ℝ) / 16) ≤ (73851321 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (817565923 / 250000000) / 16) (73851321 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((321 / 16000) : ℝ) (2569 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (102194111 / 31250000) (817565923 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (321 / 16000) (2569 / 128000) (104094088367 / 100000000000) (2081914297 / 2000000000) (102194111 / 31250000) (817565923 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (321 / 16000) (2569 / 128000) (102194111 / 31250000) (817565923 / 250000000) (54856433 / 1000000000000) (6858127 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (102194111 / 31250000) (817565923 / 250000000) (73850599 / 40000000) (73851321 / 40000000) (54856433 / 1000000000000) (6858127 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0009 :
    ∀ t ∈ Set.Icc ((2569 / 128000) : ℝ) (257 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1040957148499 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2569 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2569 / 128000)) (1040957148499 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((257 / 12800) : ℝ)) ≤ (520486706791 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (257 / 12800)) (520486706791 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((230785333 / 125000000) : ℝ) ≤ Real.exp (3 * (65405253 / 20000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (65405253 / 20000000) / 16) (230785333 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((327031479 / 100000000) : ℝ) / 16) ≤ (923150357 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (327031479 / 100000000) / 16) (923150357 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2569 / 128000) : ℝ) (257 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (65405253 / 20000000) (327031479 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2569 / 128000) (257 / 12800) (1040957148499 / 1000000000000) (520486706791 / 500000000000) (65405253 / 20000000) (327031479 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2569 / 128000) (257 / 12800) (65405253 / 20000000) (327031479 / 100000000) (2193921 / 40000000000) (27428303 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (65405253 / 20000000) (327031479 / 100000000) (230785333 / 125000000) (923150357 / 500000000) (2193921 / 40000000000) (27428303 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0010 :
    ∀ t ∈ Set.Icc ((257 / 12800) : ℝ) (2571 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1040973413581 / 1000000000000) : ℝ) ≤ Real.exp (2 * (257 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (257 / 12800)) (1040973413581 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2571 / 128000) : ℝ)) ≤ (1040989678919 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2571 / 128000)) (1040989678919 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1846300353 / 1000000000) : ℝ) ≤ Real.exp (3 * (817578437 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (817578437 / 250000000) / 16) (1846300353 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3270365889 / 1000000000) : ℝ) / 16) ≤ (461579601 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3270365889 / 1000000000) / 16) (461579601 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((257 / 12800) : ℝ) (2571 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (817578437 / 250000000) (3270365889 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (257 / 12800) (2571 / 128000) (1040973413581 / 1000000000000) (1040989678919 / 1000000000000) (817578437 / 250000000) (3270365889 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (257 / 12800) (2571 / 128000) (817578437 / 250000000) (3270365889 / 1000000000) (54839617 / 1000000000000) (27424099 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (817578437 / 250000000) (3270365889 / 1000000000) (1846300353 / 1000000000) (461579601 / 250000000) (54839617 / 1000000000000) (27424099 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0011 :
    ∀ t ∈ Set.Icc ((2571 / 128000) : ℝ) (643 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((520494839459 / 500000000000) : ℝ) ≤ Real.exp (2 * (2571 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2571 / 128000)) (520494839459 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((643 / 32000) : ℝ)) ≤ (104100594451 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (643 / 32000)) (104100594451 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((923159021 / 500000000) : ℝ) ≤ Real.exp (3 * (3270364847 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3270364847 / 1000000000) / 16) (923159021 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3270416989 / 1000000000) : ℝ) / 16) ≤ (923168047 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3270416989 / 1000000000) / 16) (923168047 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2571 / 128000) : ℝ) (643 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3270364847 / 1000000000) (3270416989 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2571 / 128000) (643 / 32000) (520494839459 / 500000000000) (104100594451 / 100000000000) (3270364847 / 1000000000) (3270416989 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2571 / 128000) (643 / 32000) (3270364847 / 1000000000) (3270416989 / 1000000000) (54831211 / 1000000000000) (5483979 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3270364847 / 1000000000) (3270416989 / 1000000000) (923159021 / 500000000) (923168047 / 500000000) (54831211 / 1000000000000) (5483979 / 100000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0012 :
    ∀ t ∈ Set.Icc ((643 / 32000) : ℝ) (2573 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1041005944509 / 1000000000000) : ℝ) ≤ Real.exp (2 * (643 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (643 / 32000)) (1041005944509 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2573 / 128000) : ℝ)) ≤ (208204442071 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2573 / 128000)) (208204442071 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((461583933 / 250000000) : ℝ) ≤ Real.exp (3 * (3270415947 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3270415947 / 1000000000) / 16) (461583933 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3270468089 / 1000000000) : ℝ) / 16) ≤ (230794223 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3270468089 / 1000000000) / 16) (230794223 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((643 / 32000) : ℝ) (2573 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3270415947 / 1000000000) (3270468089 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (643 / 32000) (2573 / 128000) (1041005944509 / 1000000000000) (208204442071 / 200000000000) (3270415947 / 1000000000) (3270468089 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (643 / 32000) (2573 / 128000) (3270415947 / 1000000000) (3270468089 / 1000000000) (27411403 / 500000000000) (6853923 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3270415947 / 1000000000) (3270468089 / 1000000000) (461583933 / 250000000) (230794223 / 125000000) (27411403 / 500000000000) (6853923 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0013 :
    ∀ t ∈ Set.Icc ((2573 / 128000) : ℝ) (1287 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((520511105177 / 500000000000) : ℝ) ≤ Real.exp (2 * (2573 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2573 / 128000)) (520511105177 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1287 / 64000) : ℝ)) ≤ (520519238227 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1287 / 64000)) (520519238227 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1846353423 / 1000000000) : ℝ) ≤ Real.exp (3 * (3270467047 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3270467047 / 1000000000) / 16) (1846353423 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3270519191 / 1000000000) : ℝ) / 16) ≤ (461592869 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3270519191 / 1000000000) / 16) (461592869 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2573 / 128000) : ℝ) (1287 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3270467047 / 1000000000) (3270519191 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2573 / 128000) (1287 / 64000) (520511105177 / 500000000000) (520519238227 / 500000000000) (3270467047 / 1000000000) (3270519191 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2573 / 128000) (1287 / 64000) (3270467047 / 1000000000) (3270519191 / 1000000000) (27407201 / 500000000000) (54822979 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3270467047 / 1000000000) (3270519191 / 1000000000) (1846353423 / 1000000000) (461592869 / 250000000) (27407201 / 500000000000) (54822979 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0014 :
    ∀ t ∈ Set.Icc ((1287 / 64000) : ℝ) (103 / 5120), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1041038476453 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1287 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1287 / 64000)) (1041038476453 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((103 / 5120) : ℝ)) ≤ (1041054742807 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (103 / 5120)) (1041054742807 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((923185557 / 500000000) : ℝ) ≤ Real.exp (3 * (3270518149 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3270518149 / 1000000000) / 16) (923185557 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3270570293 / 1000000000) : ℝ) / 16) ≤ (1846389167 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3270570293 / 1000000000) / 16) (1846389167 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1287 / 64000) : ℝ) (103 / 5120),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3270518149 / 1000000000) (3270570293 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1287 / 64000) (103 / 5120) (1041038476453 / 1000000000000) (1041054742807 / 1000000000000) (3270518149 / 1000000000) (3270570293 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1287 / 64000) (103 / 5120) (3270518149 / 1000000000) (3270570293 / 1000000000) (54805999 / 1000000000000) (2192583 / 40000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3270518149 / 1000000000) (3270570293 / 1000000000) (923185557 / 500000000) (1846389167 / 1000000000) (54805999 / 1000000000000) (2192583 / 40000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0015 :
    ∀ t ∈ Set.Icc ((103 / 5120) : ℝ) (161 / 8000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((520527371403 / 500000000000) : ℝ) ≤ Real.exp (2 * (103 / 5120)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (103 / 5120)) (520527371403 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((161 / 8000) : ℝ)) ≤ (520535504707 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (161 / 8000)) (520535504707 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((369277761 / 200000000) : ℝ) ≤ Real.exp (3 * (3270569251 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3270569251 / 1000000000) / 16) (369277761 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((817655349 / 250000000) : ℝ) / 16) ≤ (1846406859 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (817655349 / 250000000) / 16) (1846406859 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((103 / 5120) : ℝ) (161 / 8000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3270569251 / 1000000000) (817655349 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (103 / 5120) (161 / 8000) (520527371403 / 500000000000) (520535504707 / 500000000000) (3270569251 / 1000000000) (817655349 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (103 / 5120) (161 / 8000) (3270569251 / 1000000000) (817655349 / 250000000) (27398799 / 500000000000) (13701543 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3270569251 / 1000000000) (817655349 / 250000000) (369277761 / 200000000) (1846406859 / 1000000000) (27398799 / 500000000000) (13701543 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0016 :
    ∀ t ∈ Set.Icc ((161 / 8000) : ℝ) (2577 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1041071009413 / 1000000000000) : ℝ) ≤ Real.exp (2 * (161 / 8000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (161 / 8000)) (1041071009413 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2577 / 128000) : ℝ)) ≤ (260271819069 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2577 / 128000)) (260271819069 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1846406497 / 1000000000) : ℝ) ≤ Real.exp (3 * (1635310177 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1635310177 / 500000000) / 16) (1846406497 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1308269 / 400000) : ℝ) / 16) ≤ (1846424551 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1308269 / 400000) / 16) (1846424551 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((161 / 8000) : ℝ) (2577 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1635310177 / 500000000) (1308269 / 400000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (161 / 8000) (2577 / 128000) (1041071009413 / 1000000000000) (260271819069 / 250000000000) (1635310177 / 500000000) (1308269 / 400000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (161 / 8000) (2577 / 128000) (1635310177 / 500000000) (1308269 / 400000) (54789197 / 1000000000000) (54797771 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1635310177 / 500000000) (1308269 / 400000) (1846406497 / 1000000000) (1846424551 / 1000000000) (54789197 / 1000000000000) (54797771 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0017 :
    ∀ t ∈ Set.Icc ((2577 / 128000) : ℝ) (1289 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((41643491051 / 40000000000) : ℝ) ≤ Real.exp (2 * (2577 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2577 / 128000)) (41643491051 / 40000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1289 / 64000) : ℝ)) ≤ (32534485731 / 31250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1289 / 64000)) (32534485731 / 31250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1846424189 / 1000000000) : ℝ) ≤ Real.exp (3 * (1635335729 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1635335729 / 500000000) / 16) (1846424189 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((654144721 / 200000000) : ℝ) / 16) ≤ (461610561 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (654144721 / 200000000) / 16) (461610561 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2577 / 128000) : ℝ) (1289 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1635335729 / 500000000) (654144721 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2577 / 128000) (1289 / 64000) (41643491051 / 40000000000) (32534485731 / 31250000000) (1635335729 / 500000000) (654144721 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2577 / 128000) (1289 / 64000) (1635335729 / 500000000) (654144721 / 200000000) (27390399 / 500000000000) (5478937 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1635335729 / 500000000) (654144721 / 200000000) (1846424189 / 1000000000) (461610561 / 250000000) (27390399 / 500000000000) (5478937 / 100000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0018 :
    ∀ t ∈ Set.Icc ((1289 / 64000) : ℝ) (2579 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1041103543391 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1289 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1289 / 64000)) (1041103543391 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2579 / 128000) : ℝ)) ≤ (520559905381 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2579 / 128000)) (520559905381 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((923220941 / 500000000) : ℝ) ≤ Real.exp (3 * (3270722563 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3270722563 / 1000000000) / 16) (923220941 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((327077471 / 100000000) : ℝ) / 16) ≤ (1846459937 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (327077471 / 100000000) / 16) (1846459937 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1289 / 64000) : ℝ) (2579 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3270722563 / 1000000000) (327077471 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1289 / 64000) (2579 / 128000) (1041103543391 / 1000000000000) (520559905381 / 500000000000) (3270722563 / 1000000000) (327077471 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1289 / 64000) (2579 / 128000) (3270722563 / 1000000000) (327077471 / 100000000) (136931 / 2500000000) (54780971 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3270722563 / 1000000000) (327077471 / 100000000) (923220941 / 500000000) (1846459937 / 1000000000) (136931 / 2500000000) (54780971 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0019 :
    ∀ t ∈ Set.Icc ((2579 / 128000) : ℝ) (129 / 6400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1041119810761 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2579 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2579 / 128000)) (1041119810761 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((129 / 6400) : ℝ)) ≤ (520568039193 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (129 / 6400)) (520568039193 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((73858383 / 40000000) : ℝ) ≤ Real.exp (3 * (817693417 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (817693417 / 250000000) / 16) (73858383 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((408853227 / 125000000) : ℝ) / 16) ≤ (1846477631 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (408853227 / 125000000) / 16) (1846477631 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2579 / 128000) : ℝ) (129 / 6400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (817693417 / 250000000) (408853227 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2579 / 128000) (129 / 6400) (1041119810761 / 1000000000000) (520568039193 / 500000000000) (817693417 / 250000000) (408853227 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2579 / 128000) (129 / 6400) (817693417 / 250000000) (408853227 / 125000000) (54764003 / 1000000000000) (54772573 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (817693417 / 250000000) (408853227 / 125000000) (73858383 / 40000000) (1846477631 / 1000000000) (54764003 / 1000000000000) (54772573 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch000 :
    ∀ t ∈ Set.Icc ((1 / 50) : ℝ) (129 / 6400),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0000
      hpThetaDensityTwoTermCompact_cell0001)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0002
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0003
      hpThetaDensityTwoTermCompact_cell0004)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0005
      hpThetaDensityTwoTermCompact_cell0006)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0007
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0008
      hpThetaDensityTwoTermCompact_cell0009))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0010
      hpThetaDensityTwoTermCompact_cell0011)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0012
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0013
      hpThetaDensityTwoTermCompact_cell0014)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0015
      hpThetaDensityTwoTermCompact_cell0016)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0017
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0018
      hpThetaDensityTwoTermCompact_cell0019)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch000
end HodgeProofHP
