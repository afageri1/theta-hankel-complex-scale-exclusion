/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0780 :
    ∀ t ∈ Set.Icc ((2703 / 64000) : ℝ) (2707 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1088138839361 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2703 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2703 / 64000)) (1088138839361 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2707 / 64000) : ℝ)) ≤ (1088274865219 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2707 / 64000)) (1088274865219 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((189831481 / 100000000) : ℝ) ≤ Real.exp (3 * (213655517 / 62500000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (213655517 / 62500000) / 16) (189831481 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3418916699 / 1000000000) : ℝ) / 16) ≤ (1898467309 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3418916699 / 1000000000) / 16) (1898467309 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2703 / 64000) : ℝ) (2707 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (213655517 / 62500000) (3418916699 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2703 / 64000) (2707 / 64000) (1088138839361 / 1000000000000) (1088274865219 / 1000000000000) (213655517 / 62500000) (3418916699 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2703 / 64000) (2707 / 64000) (213655517 / 62500000) (3418916699 / 1000000000) (35119637 / 1000000000000) (17582403 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (213655517 / 62500000) (3418916699 / 1000000000) (189831481 / 100000000) (1898467309 / 1000000000) (35119637 / 1000000000000) (17582403 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0781 :
    ∀ t ∈ Set.Icc ((2707 / 64000) : ℝ) (543 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((544137432609 / 500000000000) : ℝ) ≤ Real.exp (2 * (2707 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2707 / 64000)) (544137432609 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((543 / 12800) : ℝ)) ≤ (1088546967947 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (543 / 12800)) (1088546967947 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1898466921 / 1000000000) : ℝ) ≤ Real.exp (3 * (341891561 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (341891561 / 100000000) / 16) (1898466921 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((683954307 / 200000000) : ℝ) / 16) ≤ (1898771623 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (683954307 / 200000000) / 16) (1898771623 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2707 / 64000) : ℝ) (543 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (341891561 / 100000000) (683954307 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2707 / 64000) (543 / 12800) (544137432609 / 500000000000) (1088546967947 / 1000000000000) (341891561 / 100000000) (683954307 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2707 / 64000) (543 / 12800) (341891561 / 100000000) (683954307 / 200000000) (4378711 / 125000000000) (35119753 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (341891561 / 100000000) (683954307 / 200000000) (1898466921 / 1000000000) (1898771623 / 1000000000) (4378711 / 125000000000) (35119753 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0782 :
    ∀ t ∈ Set.Icc ((543 / 12800) : ℝ) (2723 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((544273483973 / 500000000000) : ℝ) ≤ Real.exp (2 * (543 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (543 / 12800)) (544273483973 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2723 / 64000) : ℝ)) ≤ (272204784677 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2723 / 64000)) (272204784677 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((379754247 / 200000000) : ℝ) ≤ Real.exp (3 * (1709885223 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1709885223 / 500000000) / 16) (379754247 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((684125317 / 200000000) : ℝ) / 16) ≤ (949538031 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (684125317 / 200000000) / 16) (949538031 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((543 / 12800) : ℝ) (2723 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1709885223 / 500000000) (684125317 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (543 / 12800) (2723 / 64000) (544273483973 / 500000000000) (272204784677 / 250000000000) (1709885223 / 500000000) (684125317 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (543 / 12800) (2723 / 64000) (1709885223 / 500000000) (684125317 / 200000000) (34939947 / 1000000000000) (8757451 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1709885223 / 500000000) (684125317 / 200000000) (379754247 / 200000000) (949538031 / 500000000) (34939947 / 1000000000000) (8757451 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0783 :
    ∀ t ∈ Set.Icc ((2723 / 64000) : ℝ) (2731 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1088819138707 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2723 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2723 / 64000)) (1088819138707 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2731 / 64000) : ℝ)) ≤ (544545688761 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2731 / 64000)) (544545688761 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1899075673 / 1000000000) : ℝ) ≤ Real.exp (3 * (684125099 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (684125099 / 200000000) / 16) (1899075673 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((427685231 / 125000000) : ℝ) / 16) ≤ (949690313 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (427685231 / 125000000) / 16) (949690313 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2723 / 64000) : ℝ) (2731 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (684125099 / 200000000) (427685231 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2723 / 64000) (2731 / 64000) (1088819138707 / 1000000000000) (544545688761 / 500000000000) (684125099 / 200000000) (427685231 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2723 / 64000) (2731 / 64000) (684125099 / 200000000) (427685231 / 125000000) (34850413 / 1000000000000) (34940063 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (684125099 / 200000000) (427685231 / 125000000) (1899075673 / 1000000000) (949690313 / 500000000) (34850413 / 1000000000000) (34940063 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0784 :
    ∀ t ∈ Set.Icc ((2731 / 64000) : ℝ) (2739 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1089091377521 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2731 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2731 / 64000)) (1089091377521 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2739 / 64000) : ℝ)) ≤ (1089363684403 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2739 / 64000)) (1089363684403 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1899380237 / 1000000000) : ℝ) ≤ Real.exp (3 * (1710740379 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1710740379 / 500000000) / 16) (1899380237 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1711168663 / 500000000) : ℝ) / 16) ≤ (379937063 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1711168663 / 500000000) / 16) (379937063 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2731 / 64000) : ℝ) (2739 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1710740379 / 500000000) (1711168663 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2731 / 64000) (2739 / 64000) (1089091377521 / 1000000000000) (1089363684403 / 1000000000000) (1710740379 / 500000000) (1711168663 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2731 / 64000) (2739 / 64000) (1710740379 / 500000000) (1711168663 / 500000000) (34761087 / 1000000000000) (1089079 / 31250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1710740379 / 500000000) (1711168663 / 500000000) (1899380237 / 1000000000) (379937063 / 200000000) (34761087 / 1000000000000) (1089079 / 31250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0785 :
    ∀ t ∈ Set.Icc ((2739 / 64000) : ℝ) (2747 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((544681842201 / 500000000000) : ℝ) ≤ Real.exp (2 * (2739 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2739 / 64000)) (544681842201 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2747 / 64000) : ℝ)) ≤ (1089636059369 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2747 / 64000)) (1089636059369 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((949842463 / 500000000) : ℝ) ≤ Real.exp (3 * (855584059 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (855584059 / 250000000) / 16) (949842463 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3423193017 / 1000000000) : ℝ) / 16) ≤ (1899990129 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3423193017 / 1000000000) / 16) (1899990129 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2739 / 64000) : ℝ) (2747 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (855584059 / 250000000) (3423193017 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2739 / 64000) (2747 / 64000) (544681842201 / 500000000000) (1089636059369 / 1000000000000) (855584059 / 250000000) (3423193017 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2739 / 64000) (2747 / 64000) (855584059 / 250000000) (3423193017 / 1000000000) (34671967 / 1000000000000) (17380601 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (855584059 / 250000000) (3423193017 / 1000000000) (949842463 / 500000000) (1899990129 / 1000000000) (34671967 / 1000000000000) (17380601 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0786 :
    ∀ t ∈ Set.Icc ((2747 / 64000) : ℝ) (551 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((136204507421 / 125000000000) : ℝ) ≤ Real.exp (2 * (2747 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2747 / 64000)) (136204507421 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((551 / 12800) : ℝ)) ≤ (544954251219 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (551 / 12800)) (544954251219 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((94999487 / 50000000) : ℝ) ≤ Real.exp (3 * (3423191927 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3423191927 / 1000000000) / 16) (94999487 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1712024461 / 500000000) : ℝ) / 16) ≤ (475073767 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1712024461 / 500000000) / 16) (475073767 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2747 / 64000) : ℝ) (551 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3423191927 / 1000000000) (1712024461 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2747 / 64000) (551 / 12800) (136204507421 / 125000000000) (544954251219 / 500000000000) (3423191927 / 1000000000) (1712024461 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2747 / 64000) (551 / 12800) (3423191927 / 1000000000) (1712024461 / 500000000) (34583053 / 1000000000000) (34672081 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3423191927 / 1000000000) (1712024461 / 500000000) (94999487 / 50000000) (475073767 / 250000000) (34583053 / 1000000000000) (34672081 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0787 :
    ∀ t ∈ Set.Icc ((551 / 12800) : ℝ) (2763 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1089908502437 / 1000000000000) : ℝ) ≤ Real.exp (2 * (551 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (551 / 12800)) (1089908502437 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2763 / 64000) : ℝ)) ≤ (545090506813 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2763 / 64000)) (545090506813 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((950147339 / 500000000) : ℝ) ≤ Real.exp (3 * (3424047831 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3424047831 / 1000000000) / 16) (950147339 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1712452521 / 500000000) : ℝ) / 16) ≤ (1900600133 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1712452521 / 500000000) / 16) (1900600133 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((551 / 12800) : ℝ) (2763 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3424047831 / 1000000000) (1712452521 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (551 / 12800) (2763 / 64000) (1089908502437 / 1000000000000) (545090506813 / 500000000000) (3424047831 / 1000000000) (1712452521 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (551 / 12800) (2763 / 64000) (3424047831 / 1000000000) (1712452521 / 500000000) (6898869 / 200000000000) (270181 / 7812500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3424047831 / 1000000000) (1712452521 / 500000000) (950147339 / 500000000) (1900600133 / 1000000000) (6898869 / 200000000000) (270181 / 7812500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0788 :
    ∀ t ∈ Set.Icc ((2763 / 64000) : ℝ) (2771 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((8721448109 / 8000000000) : ℝ) ≤ Real.exp (2 * (2763 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2763 / 64000)) (8721448109 / 8000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2771 / 64000) : ℝ)) ≤ (1090453592951 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2771 / 64000)) (1090453592951 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1900599743 / 1000000000) : ℝ) ≤ Real.exp (3 * (68498079 / 20000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (68498079 / 20000000) / 16) (1900599743 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((27406091 / 8000000) : ℝ) / 16) ≤ (950452661 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (27406091 / 8000000) / 16) (950452661 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2763 / 64000) : ℝ) (2771 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (68498079 / 20000000) (27406091 / 8000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2763 / 64000) (2771 / 64000) (8721448109 / 8000000000) (1090453592951 / 1000000000000) (68498079 / 20000000) (27406091 / 8000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2763 / 64000) (2771 / 64000) (68498079 / 20000000) (27406091 / 8000000) (34405843 / 1000000000000) (1724723 / 50000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (68498079 / 20000000) (27406091 / 8000000) (1900599743 / 1000000000) (950452661 / 500000000) (34405843 / 1000000000000) (1724723 / 50000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0789 :
    ∀ t ∈ Set.Icc ((2771 / 64000) : ℝ) (2779 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((21809071859 / 20000000000) : ℝ) ≤ Real.exp (2 * (2771 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2771 / 64000)) (21809071859 / 20000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2779 / 64000) : ℝ)) ≤ (272681560107 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2779 / 64000)) (272681560107 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((475226233 / 250000000) : ℝ) ≤ Real.exp (3 * (3425760283 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3425760283 / 1000000000) / 16) (475226233 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1713308961 / 500000000) : ℝ) / 16) ≤ (1901210637 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1713308961 / 500000000) / 16) (1901210637 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2771 / 64000) : ℝ) (2779 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3425760283 / 1000000000) (1713308961 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2771 / 64000) (2779 / 64000) (21809071859 / 20000000000) (272681560107 / 250000000000) (3425760283 / 1000000000) (1713308961 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2771 / 64000) (2779 / 64000) (3425760283 / 1000000000) (1713308961 / 500000000) (17158773 / 500000000000) (34405957 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3425760283 / 1000000000) (1713308961 / 500000000) (475226233 / 250000000) (1901210637 / 1000000000) (17158773 / 500000000000) (34405957 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0790 :
    ∀ t ∈ Set.Icc ((2779 / 64000) : ℝ) (2787 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1090726240427 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2779 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2779 / 64000)) (1090726240427 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2787 / 64000) : ℝ)) ≤ (1090998956077 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2787 / 64000)) (1090998956077 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1901210247 / 1000000000) : ℝ) ≤ Real.exp (3 * (3426616831 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3426616831 / 1000000000) / 16) (1901210247 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((856868671 / 250000000) : ℝ) / 16) ≤ (1901516077 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (856868671 / 250000000) / 16) (1901516077 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2779 / 64000) : ℝ) (2787 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3426616831 / 1000000000) (856868671 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2779 / 64000) (2787 / 64000) (1090726240427 / 1000000000000) (1090998956077 / 1000000000000) (3426616831 / 1000000000) (856868671 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2779 / 64000) (2787 / 64000) (3426616831 / 1000000000) (856868671 / 250000000) (17114727 / 500000000000) (1715883 / 50000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3426616831 / 1000000000) (856868671 / 250000000) (1901210247 / 1000000000) (1901516077 / 1000000000) (17114727 / 500000000000) (1715883 / 50000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0791 :
    ∀ t ∈ Set.Icc ((2787 / 64000) : ℝ) (559 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((272749739019 / 250000000000) : ℝ) ≤ Real.exp (2 * (2787 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2787 / 64000)) (272749739019 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((559 / 12800) : ℝ)) ≤ (136408967489 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (559 / 12800)) (136408967489 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1901515687 / 1000000000) : ℝ) ≤ Real.exp (3 * (428434199 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (428434199 / 125000000) / 16) (1901515687 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((171416583 / 50000000) : ℝ) / 16) ≤ (1901821643 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (171416583 / 50000000) / 16) (1901821643 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2787 / 64000) : ℝ) (559 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (428434199 / 125000000) (171416583 / 50000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2787 / 64000) (559 / 12800) (272749739019 / 250000000000) (136408967489 / 125000000000) (428434199 / 125000000) (171416583 / 50000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2787 / 64000) (559 / 12800) (428434199 / 125000000) (171416583 / 50000000) (6828313 / 200000000000) (34229567 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (428434199 / 125000000) (171416583 / 50000000) (1901515687 / 1000000000) (1901821643 / 1000000000) (6828313 / 200000000000) (34229567 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0792 :
    ∀ t ∈ Set.Icc ((559 / 12800) : ℝ) (2803 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1091271739911 / 1000000000000) : ℝ) ≤ Real.exp (2 * (559 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (559 / 12800)) (1091271739911 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2803 / 64000) : ℝ)) ≤ (68221536997 / 62500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2803 / 64000)) (68221536997 / 62500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1901821253 / 1000000000) : ℝ) ≤ Real.exp (3 * (3428330567 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3428330567 / 1000000000) / 16) (1901821253 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((68583777 / 20000000) : ℝ) / 16) ≤ (380425467 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (68583777 / 20000000) / 16) (380425467 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((559 / 12800) : ℝ) (2803 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3428330567 / 1000000000) (68583777 / 20000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (559 / 12800) (2803 / 64000) (1091271739911 / 1000000000000) (68221536997 / 62500000000) (3428330567 / 1000000000) (68583777 / 20000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (559 / 12800) (2803 / 64000) (3428330567 / 1000000000) (68583777 / 20000000) (851347 / 25000000000) (17070839 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3428330567 / 1000000000) (68583777 / 20000000) (1901821253 / 1000000000) (380425467 / 200000000) (851347 / 25000000000) (17070839 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0793 :
    ∀ t ∈ Set.Icc ((2803 / 64000) : ℝ) (2811 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1091544591951 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2803 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2803 / 64000)) (1091544591951 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2811 / 64000) : ℝ)) ≤ (545908756107 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2811 / 64000)) (545908756107 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((59441467 / 31250000) : ℝ) ≤ Real.exp (3 * (3429187757 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3429187757 / 1000000000) / 16) (59441467 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1715023127 / 500000000) : ℝ) / 16) ≤ (1902433151 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1715023127 / 500000000) / 16) (1902433151 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2803 / 64000) : ℝ) (2811 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3429187757 / 1000000000) (1715023127 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2803 / 64000) (2811 / 64000) (1091544591951 / 1000000000000) (545908756107 / 500000000000) (3429187757 / 1000000000) (1715023127 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2803 / 64000) (2811 / 64000) (3429187757 / 1000000000) (1715023127 / 500000000) (33966399 / 1000000000000) (34053993 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3429187757 / 1000000000) (1715023127 / 500000000) (59441467 / 31250000) (1902433151 / 1000000000) (33966399 / 1000000000000) (34053993 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0794 :
    ∀ t ∈ Set.Icc ((2811 / 64000) : ℝ) (2819 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1091817512213 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2811 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2811 / 64000)) (1091817512213 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2819 / 64000) : ℝ)) ≤ (546045250357 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2819 / 64000)) (546045250357 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((47560819 / 25000000) : ℝ) ≤ Real.exp (3 * (3430045161 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3430045161 / 1000000000) / 16) (47560819 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3430903873 / 1000000000) : ℝ) / 16) ≤ (951369547 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3430903873 / 1000000000) / 16) (951369547 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2811 / 64000) : ℝ) (2819 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3430045161 / 1000000000) (3430903873 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2811 / 64000) (2819 / 64000) (1091817512213 / 1000000000000) (546045250357 / 500000000000) (3430045161 / 1000000000) (3430903873 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2811 / 64000) (2819 / 64000) (3430045161 / 1000000000) (3430903873 / 1000000000) (33879121 / 1000000000000) (2122907 / 62500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3430045161 / 1000000000) (3430903873 / 1000000000) (47560819 / 25000000) (951369547 / 500000000) (33879121 / 1000000000000) (2122907 / 62500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0795 :
    ∀ t ∈ Set.Icc ((2819 / 64000) : ℝ) (2827 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1092090500713 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2819 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2819 / 64000)) (1092090500713 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2827 / 64000) : ℝ)) ≤ (109236355747 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2827 / 64000)) (109236355747 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1902738703 / 1000000000) : ℝ) ≤ Real.exp (3 * (171545139 / 50000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (171545139 / 50000000) / 16) (1902738703 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1715880853 / 500000000) : ℝ) / 16) ≤ (951522581 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1715880853 / 500000000) / 16) (951522581 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2819 / 64000) : ℝ) (2827 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (171545139 / 50000000) (1715880853 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2819 / 64000) (2827 / 64000) (1092090500713 / 1000000000000) (109236355747 / 100000000000) (171545139 / 50000000) (1715880853 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2819 / 64000) (2827 / 64000) (171545139 / 50000000) (1715880853 / 500000000) (6758409 / 200000000000) (33879233 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (171545139 / 50000000) (1715880853 / 500000000) (1902738703 / 1000000000) (951522581 / 500000000) (6758409 / 200000000000) (33879233 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0796 :
    ∀ t ∈ Set.Icc ((2827 / 64000) : ℝ) (567 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1092363557469 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2827 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2827 / 64000)) (1092363557469 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((567 / 12800) : ℝ)) ≤ (546318341249 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (567 / 12800)) (546318341249 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1903044771 / 1000000000) : ℝ) ≤ Real.exp (3 * (3431760613 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3431760613 / 1000000000) / 16) (1903044771 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1716309877 / 500000000) : ℝ) / 16) ≤ (475837839 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1716309877 / 500000000) / 16) (475837839 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2827 / 64000) : ℝ) (567 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3431760613 / 1000000000) (1716309877 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2827 / 64000) (567 / 12800) (1092363557469 / 1000000000000) (546318341249 / 500000000000) (3431760613 / 1000000000) (1716309877 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2827 / 64000) (567 / 12800) (3431760613 / 1000000000) (1716309877 / 500000000) (33705171 / 1000000000000) (33792157 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3431760613 / 1000000000) (1716309877 / 500000000) (1903044771 / 1000000000) (475837839 / 250000000) (33705171 / 1000000000000) (33792157 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0797 :
    ∀ t ∈ Set.Icc ((567 / 12800) : ℝ) (2843 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1092636682497 / 1000000000000) : ℝ) ≤ Real.exp (2 * (567 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (567 / 12800)) (1092636682497 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2843 / 64000) : ℝ)) ≤ (1092909875817 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2843 / 64000)) (1092909875817 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((380670193 / 200000000) : ℝ) ≤ Real.exp (3 * (171630933 / 50000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (171630933 / 50000000) / 16) (380670193 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((26824047 / 7812500) : ℝ) / 16) ≤ (475914419 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (26824047 / 7812500) / 16) (475914419 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((567 / 12800) : ℝ) (2843 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (171630933 / 50000000) (26824047 / 7812500) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (567 / 12800) (2843 / 64000) (1092636682497 / 1000000000000) (1092909875817 / 1000000000000) (171630933 / 50000000) (26824047 / 7812500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (567 / 12800) (2843 / 64000) (171630933 / 50000000) (26824047 / 7812500) (33618499 / 1000000000000) (33705283 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (171630933 / 50000000) (26824047 / 7812500) (380670193 / 200000000) (475914419 / 250000000) (33618499 / 1000000000000) (33705283 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0798 :
    ∀ t ∈ Set.Icc ((2843 / 64000) : ℝ) (2851 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((136613734477 / 125000000000) : ℝ) ≤ Real.exp (2 * (2843 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2843 / 64000)) (136613734477 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2851 / 64000) : ℝ)) ≤ (546591568721 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2851 / 64000)) (546591568721 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((380731457 / 200000000) : ℝ) ≤ Real.exp (3 * (1716738461 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1716738461 / 500000000) / 16) (380731457 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3434336493 / 1000000000) : ℝ) / 16) ≤ (951982061 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3434336493 / 1000000000) / 16) (951982061 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2843 / 64000) : ℝ) (2851 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1716738461 / 500000000) (3434336493 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2843 / 64000) (2851 / 64000) (136613734477 / 125000000000) (546591568721 / 500000000000) (1716738461 / 500000000) (3434336493 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2843 / 64000) (2851 / 64000) (1716738461 / 500000000) (3434336493 / 1000000000) (33532029 / 1000000000000) (33618611 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1716738461 / 500000000) (3434336493 / 1000000000) (380731457 / 200000000) (951982061 / 500000000) (33532029 / 1000000000000) (33618611 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0799 :
    ∀ t ∈ Set.Icc ((2851 / 64000) : ℝ) (2859 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1093183137441 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2851 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2851 / 64000)) (1093183137441 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2859 / 64000) : ℝ)) ≤ (1093456467391 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2859 / 64000)) (1093456467391 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((190396373 / 100000000) : ℝ) ≤ Real.exp (3 * (3434335399 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3434335399 / 1000000000) / 16) (190396373 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((214699699 / 62500000) : ℝ) / 16) ≤ (952135347 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (214699699 / 62500000) / 16) (952135347 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2851 / 64000) : ℝ) (2859 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3434335399 / 1000000000) (214699699 / 62500000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2851 / 64000) (2859 / 64000) (1093183137441 / 1000000000000) (1093456467391 / 1000000000000) (3434335399 / 1000000000) (214699699 / 62500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2851 / 64000) (2859 / 64000) (3434335399 / 1000000000) (214699699 / 62500000) (33445759 / 1000000000000) (1676607 / 50000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3434335399 / 1000000000) (214699699 / 62500000) (190396373 / 100000000) (952135347 / 500000000) (33445759 / 1000000000000) (1676607 / 50000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch039 :
    ∀ t ∈ Set.Icc ((2703 / 64000) : ℝ) (2859 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0780
      hpThetaDensityTwoTermCompact_cell0781)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0782
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0783
      hpThetaDensityTwoTermCompact_cell0784)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0785
      hpThetaDensityTwoTermCompact_cell0786)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0787
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0788
      hpThetaDensityTwoTermCompact_cell0789))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0790
      hpThetaDensityTwoTermCompact_cell0791)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0792
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0793
      hpThetaDensityTwoTermCompact_cell0794)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0795
      hpThetaDensityTwoTermCompact_cell0796)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0797
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0798
      hpThetaDensityTwoTermCompact_cell0799)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch039
end HodgeProofHP
