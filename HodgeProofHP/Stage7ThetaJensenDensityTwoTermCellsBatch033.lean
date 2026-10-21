/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0660 :
    ∀ t ∈ Set.Icc ((2223 / 64000) : ℝ) (2227 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1071938562601 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2223 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2223 / 64000)) (1071938562601 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2227 / 64000) : ℝ)) ≤ (1072072563297 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2227 / 64000)) (1072072563297 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1880285829 / 1000000000) : ℝ) ≤ Real.exp (3 * (841898403 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (841898403 / 250000000) / 16) (1880285829 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3368015661 / 1000000000) : ℝ) / 16) ≤ (1880434631 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3368015661 / 1000000000) / 16) (1880434631 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2223 / 64000) : ℝ) (2227 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (841898403 / 250000000) (3368015661 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2223 / 64000) (2227 / 64000) (1071938562601 / 1000000000000) (1072072563297 / 1000000000000) (841898403 / 250000000) (3368015661 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2223 / 64000) (2227 / 64000) (841898403 / 250000000) (3368015661 / 1000000000) (20456821 / 500000000000) (40965479 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (841898403 / 250000000) (3368015661 / 1000000000) (1880285829 / 1000000000) (1880434631 / 1000000000) (20456821 / 500000000000) (40965479 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0661 :
    ∀ t ∈ Set.Icc ((2227 / 64000) : ℝ) (2231 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((33502267603 / 31250000000) : ℝ) ≤ Real.exp (2 * (2227 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2227 / 64000)) (33502267603 / 31250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2231 / 64000) : ℝ)) ≤ (1072206580743 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2231 / 64000)) (1072206580743 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1880434251 / 1000000000) : ℝ) ≤ Real.exp (3 * (842003647 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (842003647 / 250000000) / 16) (1880434251 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3368436689 / 1000000000) : ℝ) / 16) ≤ (1880583083 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3368436689 / 1000000000) / 16) (1880583083 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2227 / 64000) : ℝ) (2231 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (842003647 / 250000000) (3368436689 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2227 / 64000) (2231 / 64000) (33502267603 / 31250000000) (1072206580743 / 1000000000000) (842003647 / 250000000) (3368436689 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2227 / 64000) (2231 / 64000) (842003647 / 250000000) (3368436689 / 1000000000) (20430999 / 500000000000) (1636551 / 40000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (842003647 / 250000000) (3368436689 / 1000000000) (1880434251 / 1000000000) (1880583083 / 1000000000) (20430999 / 500000000000) (1636551 / 40000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0662 :
    ∀ t ∈ Set.Icc ((2231 / 64000) : ℝ) (447 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((536103290371 / 500000000000) : ℝ) ≤ Real.exp (2 * (2231 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2231 / 64000)) (536103290371 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((447 / 12800) : ℝ)) ≤ (1072340614943 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (447 / 12800)) (1072340614943 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((117536419 / 62500000) : ℝ) ≤ Real.exp (3 * (105263613 / 31250000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (105263613 / 31250000) / 16) (117536419 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((336885777 / 100000000) : ℝ) / 16) ≤ (940365783 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (336885777 / 100000000) / 16) (940365783 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2231 / 64000) : ℝ) (447 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (105263613 / 31250000) (336885777 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2231 / 64000) (447 / 12800) (536103290371 / 500000000000) (1072340614943 / 1000000000000) (105263613 / 31250000) (336885777 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2231 / 64000) (447 / 12800) (105263613 / 31250000) (336885777 / 100000000) (10202603 / 250000000000) (4086213 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (105263613 / 31250000) (336885777 / 100000000) (117536419 / 62500000) (940365783 / 500000000) (10202603 / 250000000000) (4086213 / 100000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0663 :
    ∀ t ∈ Set.Icc ((447 / 12800) : ℝ) (2239 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((536170307471 / 500000000000) : ℝ) ≤ Real.exp (2 * (447 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (447 / 12800)) (536170307471 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2239 / 64000) : ℝ)) ≤ (536237332949 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2239 / 64000)) (536237332949 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1880731187 / 1000000000) : ℝ) ≤ Real.exp (3 * (3368856697 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3368856697 / 1000000000) / 16) (1880731187 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((421159863 / 125000000) : ℝ) / 16) ≤ (23511001 / 12500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (421159863 / 125000000) / 16) (23511001 / 12500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((447 / 12800) : ℝ) (2239 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3368856697 / 1000000000) (421159863 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (447 / 12800) (2239 / 64000) (536170307471 / 500000000000) (536237332949 / 500000000000) (3368856697 / 1000000000) (421159863 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (447 / 12800) (2239 / 64000) (3368856697 / 1000000000) (421159863 / 125000000) (10189721 / 250000000000) (2550659 / 62500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3368856697 / 1000000000) (421159863 / 125000000) (1880731187 / 1000000000) (23511001 / 12500000) (10189721 / 250000000000) (2550659 / 62500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0664 :
    ∀ t ∈ Set.Icc ((2239 / 64000) : ℝ) (2243 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1072474665897 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2239 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2239 / 64000)) (1072474665897 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2243 / 64000) : ℝ)) ≤ (107260873361 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2243 / 64000)) (107260873361 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((18808797 / 10000000) : ℝ) ≤ Real.exp (3 * (336927783 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (336927783 / 100000000) / 16) (18808797 / 10000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((336970009 / 100000000) : ℝ) / 16) ≤ (1881028623 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (336970009 / 100000000) / 16) (1881028623 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2239 / 64000) : ℝ) (2243 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (336927783 / 100000000) (336970009 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2239 / 64000) (2243 / 64000) (1072474665897 / 1000000000000) (107260873361 / 100000000000) (336927783 / 100000000) (336970009 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2239 / 64000) (2243 / 64000) (336927783 / 100000000) (336970009 / 100000000) (8141483 / 200000000000) (40759017 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (336927783 / 100000000) (336970009 / 100000000) (18808797 / 10000000) (1881028623 / 1000000000) (8141483 / 200000000000) (40759017 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0665 :
    ∀ t ∈ Set.Icc ((2243 / 64000) : ℝ) (2247 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1072608733609 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2243 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2243 / 64000)) (1072608733609 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2247 / 64000) : ℝ)) ≤ (536371409041 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2247 / 64000)) (536371409041 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1881028243 / 1000000000) : ℝ) ≤ Real.exp (3 * (421212377 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (421212377 / 125000000) / 16) (1881028243 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3370121329 / 1000000000) : ℝ) / 16) ≤ (1881177197 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3370121329 / 1000000000) / 16) (1881177197 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2243 / 64000) : ℝ) (2247 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (421212377 / 125000000) (3370121329 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2243 / 64000) (2247 / 64000) (1072608733609 / 1000000000000) (536371409041 / 500000000000) (421212377 / 125000000) (3370121329 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2243 / 64000) (2247 / 64000) (421212377 / 125000000) (3370121329 / 1000000000) (8131201 / 200000000000) (10176887 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (421212377 / 125000000) (3370121329 / 1000000000) (1881028243 / 1000000000) (1881177197 / 1000000000) (8131201 / 200000000000) (10176887 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0666 :
    ∀ t ∈ Set.Icc ((2247 / 64000) : ℝ) (2251 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1072742818081 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2247 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2247 / 64000)) (1072742818081 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2251 / 64000) : ℝ)) ≤ (214575383863 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2251 / 64000)) (214575383863 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1881176817 / 1000000000) : ℝ) ≤ Real.exp (3 * (674024051 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (674024051 / 200000000) / 16) (1881176817 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((168527131 / 50000000) : ℝ) / 16) ≤ (1881325801 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (168527131 / 50000000) / 16) (1881325801 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2247 / 64000) : ℝ) (2251 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (674024051 / 200000000) (168527131 / 50000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2247 / 64000) (2251 / 64000) (1072742818081 / 1000000000000) (214575383863 / 200000000000) (674024051 / 200000000) (168527131 / 50000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2247 / 64000) (2251 / 64000) (674024051 / 200000000) (168527131 / 50000000) (20302327 / 500000000000) (20328069 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (674024051 / 200000000) (168527131 / 50000000) (1881176817 / 1000000000) (1881325801 / 1000000000) (20302327 / 500000000000) (20328069 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0667 :
    ∀ t ∈ Set.Icc ((2251 / 64000) : ℝ) (451 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((536438459657 / 500000000000) : ℝ) ≤ Real.exp (2 * (2251 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2251 / 64000)) (536438459657 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((451 / 12800) : ℝ)) ≤ (8382898729 / 7812500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (451 / 12800)) (8382898729 / 7812500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1881325421 / 1000000000) : ℝ) ≤ Real.exp (3 * (1685270773 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1685270773 / 500000000) / 16) (1881325421 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((842740991 / 250000000) : ℝ) / 16) ≤ (376294887 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (842740991 / 250000000) / 16) (376294887 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2251 / 64000) : ℝ) (451 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1685270773 / 500000000) (842740991 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2251 / 64000) (451 / 12800) (536438459657 / 500000000000) (8382898729 / 7812500000) (1685270773 / 500000000) (842740991 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2251 / 64000) (451 / 12800) (1685270773 / 500000000) (842740991 / 250000000) (40553361 / 1000000000000) (20302393 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1685270773 / 500000000) (842740991 / 250000000) (1881325421 / 1000000000) (376294887 / 200000000) (40553361 / 1000000000000) (20302393 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0668 :
    ∀ t ∈ Set.Icc ((451 / 12800) : ℝ) (2259 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1073011037311 / 1000000000000) : ℝ) ≤ Real.exp (2 * (451 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (451 / 12800)) (1073011037311 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2259 / 64000) : ℝ)) ≤ (42925806883 / 40000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2259 / 64000)) (42925806883 / 40000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((376294811 / 200000000) : ℝ) ≤ Real.exp (3 * (337096289 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (337096289 / 100000000) / 16) (376294811 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3371385361 / 1000000000) : ℝ) / 16) ≤ (18816231 / 10000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3371385361 / 1000000000) / 16) (18816231 / 10000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((451 / 12800) : ℝ) (2259 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (337096289 / 100000000) (3371385361 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (451 / 12800) (2259 / 64000) (1073011037311 / 1000000000000) (42925806883 / 40000000000) (337096289 / 100000000) (3371385361 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (451 / 12800) (2259 / 64000) (337096289 / 100000000) (3371385361 / 1000000000) (20251063 / 500000000000) (40553493 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (337096289 / 100000000) (3371385361 / 1000000000) (376294811 / 200000000) (18816231 / 10000000) (20251063 / 500000000000) (40553493 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0669 :
    ∀ t ∈ Set.Icc ((2259 / 64000) : ℝ) (2263 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((536572586037 / 500000000000) : ℝ) ≤ Real.exp (2 * (2259 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2259 / 64000)) (536572586037 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2263 / 64000) : ℝ)) ≤ (536639661803 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2263 / 64000)) (536639661803 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((5880071 / 3125000) : ℝ) ≤ Real.exp (3 * (3371384287 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3371384287 / 1000000000) / 16) (5880071 / 3125000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3371806811 / 1000000000) : ℝ) / 16) ≤ (376354359 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3371806811 / 1000000000) / 16) (376354359 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2259 / 64000) : ℝ) (2263 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3371384287 / 1000000000) (3371806811 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2259 / 64000) (2263 / 64000) (536572586037 / 500000000000) (536639661803 / 500000000000) (3371384287 / 1000000000) (3371806811 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2259 / 64000) (2263 / 64000) (3371384287 / 1000000000) (3371806811 / 1000000000) (40450949 / 1000000000000) (20251129 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3371384287 / 1000000000) (3371806811 / 1000000000) (5880071 / 3125000) (376354359 / 200000000) (40450949 / 1000000000000) (20251129 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0670 :
    ∀ t ∈ Set.Icc ((2263 / 64000) : ℝ) (2267 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((214655864721 / 200000000000) : ℝ) ≤ Real.exp (2 * (2263 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2263 / 64000)) (214655864721 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2267 / 64000) : ℝ)) ≤ (1073413491907 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2267 / 64000)) (1073413491907 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((376354283 / 200000000) : ℝ) ≤ Real.exp (3 * (421475717 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (421475717 / 125000000) / 16) (376354283 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3372228313 / 1000000000) : ℝ) / 16) ≤ (1881920521 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3372228313 / 1000000000) / 16) (1881920521 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2263 / 64000) : ℝ) (2267 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (421475717 / 125000000) (3372228313 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2263 / 64000) (2267 / 64000) (214655864721 / 200000000000) (1073413491907 / 1000000000000) (421475717 / 125000000) (3372228313 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2263 / 64000) (2267 / 64000) (421475717 / 125000000) (3372228313 / 1000000000) (40399831 / 1000000000000) (40451081 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (421475717 / 125000000) (3372228313 / 1000000000) (376354283 / 200000000) (1881920521 / 1000000000) (40399831 / 1000000000000) (40451081 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0671 :
    ∀ t ∈ Set.Icc ((2267 / 64000) : ℝ) (2271 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((536706745953 / 500000000000) : ℝ) ≤ Real.exp (2 * (2267 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2267 / 64000)) (536706745953 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2271 / 64000) : ℝ)) ≤ (53677383849 / 50000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2271 / 64000)) (53677383849 / 50000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((94096007 / 50000000) : ℝ) ≤ Real.exp (3 * (1686113619 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1686113619 / 500000000) / 16) (94096007 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((843162467 / 250000000) : ℝ) / 16) ≤ (470517319 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (843162467 / 250000000) / 16) (470517319 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2267 / 64000) : ℝ) (2271 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1686113619 / 500000000) (843162467 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2267 / 64000) (2271 / 64000) (536706745953 / 500000000000) (53677383849 / 50000000000) (1686113619 / 500000000) (843162467 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2267 / 64000) (2271 / 64000) (1686113619 / 500000000) (843162467 / 250000000) (40348771 / 1000000000000) (40399963 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1686113619 / 500000000) (843162467 / 250000000) (94096007 / 50000000) (470517319 / 250000000) (40348771 / 1000000000000) (40399963 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0672 :
    ∀ t ∈ Set.Icc ((2271 / 64000) : ℝ) (91 / 2560), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1073547676979 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2271 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2271 / 64000)) (1073547676979 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((91 / 2560) : ℝ)) ≤ (1073681878827 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (91 / 2560)) (1073681878827 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((58814653 / 31250000) : ℝ) ≤ Real.exp (3 * (3372648793 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3372648793 / 1000000000) / 16) (58814653 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((134922859 / 40000000) : ℝ) / 16) ≤ (941109031 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (134922859 / 40000000) / 16) (941109031 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2271 / 64000) : ℝ) (91 / 2560),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3372648793 / 1000000000) (134922859 / 40000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2271 / 64000) (91 / 2560) (1073547676979 / 1000000000000) (1073681878827 / 1000000000000) (3372648793 / 1000000000) (134922859 / 40000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2271 / 64000) (91 / 2560) (3372648793 / 1000000000) (134922859 / 40000000) (40297769 / 1000000000000) (40348903 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3372648793 / 1000000000) (134922859 / 40000000) (58814653 / 31250000) (941109031 / 500000000) (40297769 / 1000000000000) (40348903 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0673 :
    ∀ t ∈ Set.Icc ((91 / 2560) : ℝ) (2279 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((536840939413 / 500000000000) : ℝ) ≤ Real.exp (2 * (91 / 2560)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (91 / 2560)) (536840939413 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2279 / 64000) : ℝ)) ≤ (21476321949 / 20000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2279 / 64000)) (21476321949 / 20000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((941108841 / 500000000) : ℝ) ≤ Real.exp (3 * (3373070401 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3373070401 / 1000000000) / 16) (941108841 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((210843321 / 62500000) : ℝ) / 16) ≤ (1882366879 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (210843321 / 62500000) / 16) (1882366879 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((91 / 2560) : ℝ) (2279 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3373070401 / 1000000000) (210843321 / 62500000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (91 / 2560) (2279 / 64000) (536840939413 / 500000000000) (21476321949 / 20000000000) (3373070401 / 1000000000) (210843321 / 62500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (91 / 2560) (2279 / 64000) (3373070401 / 1000000000) (210843321 / 62500000) (20123413 / 500000000000) (40297901 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3373070401 / 1000000000) (210843321 / 62500000) (941108841 / 500000000) (1882366879 / 1000000000) (20123413 / 500000000000) (40297901 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0674 :
    ∀ t ∈ Set.Icc ((2279 / 64000) : ℝ) (2283 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1073816097449 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2279 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2279 / 64000)) (1073816097449 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2283 / 64000) : ℝ)) ≤ (268487583213 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2283 / 64000)) (268487583213 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1882366499 / 1000000000) : ℝ) ≤ Real.exp (3 * (3373492061 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3373492061 / 1000000000) / 16) (1882366499 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3373914849 / 1000000000) : ℝ) / 16) ≤ (941257863 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3373914849 / 1000000000) / 16) (941257863 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2279 / 64000) : ℝ) (2283 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3373492061 / 1000000000) (3373914849 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2279 / 64000) (2283 / 64000) (1073816097449 / 1000000000000) (268487583213 / 250000000000) (3373492061 / 1000000000) (3373914849 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2279 / 64000) (2283 / 64000) (3373492061 / 1000000000) (3373914849 / 1000000000) (2009797 / 50000000000) (40246957 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3373492061 / 1000000000) (3373914849 / 1000000000) (1882366499 / 1000000000) (941257863 / 500000000) (2009797 / 50000000000) (40246957 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0675 :
    ∀ t ∈ Set.Icc ((2283 / 64000) : ℝ) (2287 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1073950332851 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2283 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2283 / 64000)) (1073950332851 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2287 / 64000) : ℝ)) ≤ (537042292517 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2287 / 64000)) (537042292517 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((941257673 / 500000000) : ℝ) ≤ Real.exp (3 * (1686956887 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1686956887 / 500000000) / 16) (941257673 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1687168307 / 500000000) : ℝ) / 16) ≤ (1882664603 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1687168307 / 500000000) / 16) (1882664603 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2283 / 64000) : ℝ) (2287 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1686956887 / 500000000) (1687168307 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2283 / 64000) (2287 / 64000) (1073950332851 / 1000000000000) (537042292517 / 500000000000) (1686956887 / 500000000) (1687168307 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2283 / 64000) (2287 / 64000) (1686956887 / 500000000) (1687168307 / 500000000) (5018139 / 125000000000) (40196071 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1686956887 / 500000000) (1687168307 / 500000000) (941257673 / 500000000) (1882664603 / 1000000000) (5018139 / 125000000000) (40196071 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0676 :
    ∀ t ∈ Set.Icc ((2287 / 64000) : ℝ) (2291 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1074084585033 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2287 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2287 / 64000)) (1074084585033 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2291 / 64000) : ℝ)) ≤ (1074218853999 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2291 / 64000)) (1074218853999 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1882664223 / 1000000000) : ℝ) ≤ Real.exp (3 * (3374335539 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3374335539 / 1000000000) / 16) (1882664223 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3374758433 / 1000000000) : ℝ) / 16) ≤ (1882813511 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3374758433 / 1000000000) / 16) (1882813511 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2287 / 64000) : ℝ) (2291 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3374335539 / 1000000000) (3374758433 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2287 / 64000) (2291 / 64000) (1074084585033 / 1000000000000) (1074218853999 / 1000000000000) (3374335539 / 1000000000) (3374758433 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2287 / 64000) (2291 / 64000) (3374335539 / 1000000000) (3374758433 / 1000000000) (40094343 / 1000000000000) (40145243 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3374335539 / 1000000000) (3374758433 / 1000000000) (1882664223 / 1000000000) (1882813511 / 1000000000) (40094343 / 1000000000000) (40145243 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0677 :
    ∀ t ∈ Set.Icc ((2291 / 64000) : ℝ) (459 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((537109426999 / 500000000000) : ℝ) ≤ Real.exp (2 * (2291 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2291 / 64000)) (537109426999 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((459 / 12800) : ℝ)) ≤ (268588284937 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (459 / 12800)) (268588284937 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((188281313 / 100000000) : ℝ) ≤ Real.exp (3 * (3374757357 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3374757357 / 1000000000) / 16) (188281313 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((210948769 / 62500000) : ℝ) / 16) ≤ (1882962449 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (210948769 / 62500000) / 16) (1882962449 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2291 / 64000) : ℝ) (459 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3374757357 / 1000000000) (210948769 / 62500000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2291 / 64000) (459 / 12800) (537109426999 / 500000000000) (268588284937 / 250000000000) (3374757357 / 1000000000) (210948769 / 62500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2291 / 64000) (459 / 12800) (3374757357 / 1000000000) (210948769 / 62500000) (40043631 / 1000000000000) (40094473 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3374757357 / 1000000000) (210948769 / 62500000) (188281313 / 100000000) (1882962449 / 1000000000) (40043631 / 1000000000000) (40094473 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0678 :
    ∀ t ∈ Set.Icc ((459 / 12800) : ℝ) (2299 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1074353139747 / 1000000000000) : ℝ) ≤ Real.exp (2 * (459 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (459 / 12800)) (1074353139747 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2299 / 64000) : ℝ)) ≤ (268621860571 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2299 / 64000)) (268621860571 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((470740517 / 250000000) : ℝ) ≤ Real.exp (3 * (3375179229 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3375179229 / 1000000000) / 16) (470740517 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((843900557 / 250000000) : ℝ) / 16) ≤ (1883111417 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (843900557 / 250000000) / 16) (1883111417 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((459 / 12800) : ℝ) (2299 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3375179229 / 1000000000) (843900557 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (459 / 12800) (2299 / 64000) (1074353139747 / 1000000000000) (268621860571 / 250000000000) (3375179229 / 1000000000) (843900557 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (459 / 12800) (2299 / 64000) (3375179229 / 1000000000) (843900557 / 250000000) (39992977 / 1000000000000) (40043761 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3375179229 / 1000000000) (843900557 / 250000000) (470740517 / 250000000) (1883111417 / 1000000000) (39992977 / 1000000000000) (40043761 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0679 :
    ∀ t ∈ Set.Icc ((2299 / 64000) : ℝ) (2303 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1074487442283 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2299 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2299 / 64000)) (1074487442283 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2303 / 64000) : ℝ)) ≤ (107462176161 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2303 / 64000)) (107462176161 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((470777759 / 250000000) : ℝ) ≤ Real.exp (3 * (6592971 / 1953125) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (6592971 / 1953125) / 16) (470777759 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((844006051 / 250000000) : ℝ) / 16) ≤ (3678243 / 1953125) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (844006051 / 250000000) / 16) (3678243 / 1953125) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2299 / 64000) : ℝ) (2303 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (6592971 / 1953125) (844006051 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2299 / 64000) (2303 / 64000) (1074487442283 / 1000000000000) (107462176161 / 100000000000) (6592971 / 1953125) (844006051 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2299 / 64000) (2303 / 64000) (6592971 / 1953125) (844006051 / 250000000) (39942381 / 1000000000000) (39993107 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (6592971 / 1953125) (844006051 / 250000000) (470777759 / 250000000) (3678243 / 1953125) (39942381 / 1000000000000) (39993107 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch033 :
    ∀ t ∈ Set.Icc ((2223 / 64000) : ℝ) (2303 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0660
      hpThetaDensityTwoTermCompact_cell0661)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0662
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0663
      hpThetaDensityTwoTermCompact_cell0664)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0665
      hpThetaDensityTwoTermCompact_cell0666)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0667
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0668
      hpThetaDensityTwoTermCompact_cell0669))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0670
      hpThetaDensityTwoTermCompact_cell0671)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0672
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0673
      hpThetaDensityTwoTermCompact_cell0674)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0675
      hpThetaDensityTwoTermCompact_cell0676)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0677
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0678
      hpThetaDensityTwoTermCompact_cell0679)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch033
end HodgeProofHP
