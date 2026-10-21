/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0580 :
    ∀ t ∈ Set.Icc ((401 / 12800) : ℝ) (2007 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((266165199793 / 250000000000) : ℝ) ≤ Real.exp (2 * (401 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (401 / 12800)) (266165199793 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2007 / 64000) : ℝ)) ≤ (133090917819 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2007 / 64000)) (133090917819 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((93612119 / 50000000) : ℝ) ≤ Real.exp (3 * (3344729849 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3344729849 / 1000000000) / 16) (93612119 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3344939967 / 1000000000) : ℝ) / 16) ≤ (117019759 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3344939967 / 1000000000) / 16) (117019759 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((401 / 12800) : ℝ) (2007 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3344729849 / 1000000000) (3344939967 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (401 / 12800) (2007 / 64000) (266165199793 / 250000000000) (133090917819 / 125000000000) (3344729849 / 1000000000) (3344939967 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (401 / 12800) (2007 / 64000) (3344729849 / 1000000000) (3344939967 / 1000000000) (43846313 / 1000000000000) (21936981 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3344729849 / 1000000000) (3344939967 / 1000000000) (93612119 / 50000000) (117019759 / 62500000) (43846313 / 1000000000000) (21936981 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0581 :
    ∀ t ∈ Set.Icc ((2007 / 64000) : ℝ) (2009 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1064727342551 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2007 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2007 / 64000)) (1064727342551 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2009 / 64000) : ℝ)) ≤ (106479389009 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2009 / 64000)) (106479389009 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1872315769 / 1000000000) : ℝ) ≤ Real.exp (3 * (3344938901 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3344938901 / 1000000000) / 16) (1872315769 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((418143629 / 125000000) : ℝ) / 16) ≤ (93619477 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (418143629 / 125000000) / 16) (93619477 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2007 / 64000) : ℝ) (2009 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3344938901 / 1000000000) (418143629 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2007 / 64000) (2009 / 64000) (1064727342551 / 1000000000000) (106479389009 / 100000000000) (3344938901 / 1000000000) (418143629 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2007 / 64000) (2009 / 64000) (3344938901 / 1000000000) (418143629 / 125000000) (21909411 / 500000000000) (8769291 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3344938901 / 1000000000) (418143629 / 125000000) (1872315769 / 1000000000) (93619477 / 50000000) (21909411 / 500000000000) (8769291 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0582 :
    ∀ t ∈ Set.Icc ((2009 / 64000) : ℝ) (2011 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1064793890089 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2009 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2009 / 64000)) (1064793890089 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2011 / 64000) : ℝ)) ≤ (266215110447 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2011 / 64000)) (266215110447 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((468097291 / 250000000) : ℝ) ≤ Real.exp (3 * (1672573983 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1672573983 / 500000000) / 16) (468097291 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((334535811 / 100000000) : ℝ) / 16) ≤ (1872462943 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (334535811 / 100000000) / 16) (1872462943 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2009 / 64000) : ℝ) (2011 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1672573983 / 500000000) (334535811 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2009 / 64000) (2011 / 64000) (1064793890089 / 1000000000000) (266215110447 / 250000000000) (1672573983 / 500000000) (334535811 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2009 / 64000) (2011 / 64000) (1672573983 / 500000000) (334535811 / 100000000) (21895673 / 500000000000) (43818963 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1672573983 / 500000000) (334535811 / 100000000) (468097291 / 250000000) (1872462943 / 1000000000) (21895673 / 500000000000) (43818963 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0583 :
    ∀ t ∈ Set.Icc ((2011 / 64000) : ℝ) (2013 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1064860441787 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2011 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2011 / 64000)) (1064860441787 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2013 / 64000) : ℝ)) ≤ (532463498823 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2013 / 64000)) (532463498823 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((234057821 / 125000000) : ℝ) ≤ Real.exp (3 * (669071409 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (669071409 / 200000000) / 16) (234057821 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1672783601 / 500000000) : ℝ) / 16) ≤ (936268177 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1672783601 / 500000000) / 16) (936268177 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2011 / 64000) : ℝ) (2013 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (669071409 / 200000000) (1672783601 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2011 / 64000) (2013 / 64000) (1064860441787 / 1000000000000) (532463498823 / 500000000000) (669071409 / 200000000) (1672783601 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2011 / 64000) (2013 / 64000) (669071409 / 200000000) (1672783601 / 500000000) (8752777 / 200000000000) (43791487 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (669071409 / 200000000) (1672783601 / 500000000) (234057821 / 125000000) (936268177 / 500000000) (8752777 / 200000000000) (43791487 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0584 :
    ∀ t ∈ Set.Icc ((2013 / 64000) : ℝ) (403 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((212985399529 / 200000000000) : ℝ) ≤ Real.exp (2 * (2013 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2013 / 64000)) (212985399529 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((403 / 12800) : ℝ)) ≤ (1064993557663 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (403 / 12800)) (1064993557663 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((936267989 / 500000000) : ℝ) ≤ Real.exp (3 * (418195767 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (418195767 / 125000000) / 16) (936267989 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1672888153 / 500000000) : ℝ) / 16) ≤ (1872609771 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1672888153 / 500000000) / 16) (1872609771 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2013 / 64000) : ℝ) (403 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (418195767 / 125000000) (1672888153 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2013 / 64000) (403 / 12800) (212985399529 / 200000000000) (1064993557663 / 1000000000000) (418195767 / 125000000) (1672888153 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2013 / 64000) (403 / 12800) (418195767 / 125000000) (1672888153 / 500000000) (1093411 / 25000000000) (43764027 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (418195767 / 125000000) (1672888153 / 500000000) (936267989 / 500000000) (1872609771 / 1000000000) (1093411 / 25000000000) (43764027 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0585 :
    ∀ t ∈ Set.Icc ((403 / 12800) : ℝ) (2017 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((532496778831 / 500000000000) : ℝ) ≤ Real.exp (2 * (403 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (403 / 12800)) (532496778831 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2017 / 64000) : ℝ)) ≤ (1065060121841 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2017 / 64000)) (1065060121841 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((468152349 / 250000000) : ℝ) ≤ Real.exp (3 * (83644381 / 25000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (83644381 / 25000000) / 16) (468152349 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((209124089 / 62500000) : ℝ) / 16) ≤ (1872683197 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (209124089 / 62500000) / 16) (1872683197 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((403 / 12800) : ℝ) (2017 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (83644381 / 25000000) (209124089 / 62500000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (403 / 12800) (2017 / 64000) (532496778831 / 500000000000) (1065060121841 / 1000000000000) (83644381 / 25000000) (209124089 / 62500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (403 / 12800) (2017 / 64000) (83644381 / 25000000) (209124089 / 62500000) (43709011 / 1000000000000) (43736581 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (83644381 / 25000000) (209124089 / 62500000) (468152349 / 250000000) (1872683197 / 1000000000) (43709011 / 1000000000000) (43736581 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0586 :
    ∀ t ∈ Set.Icc ((2017 / 64000) : ℝ) (2019 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((13313251523 / 12500000000) : ℝ) ≤ Real.exp (2 * (2017 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2017 / 64000)) (13313251523 / 12500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2019 / 64000) : ℝ)) ≤ (532563345089 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2019 / 64000)) (532563345089 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((936341411 / 500000000) : ℝ) ≤ Real.exp (3 * (1672992179 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1672992179 / 500000000) / 16) (936341411 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1673097277 / 500000000) : ℝ) / 16) ≤ (187275663 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1673097277 / 500000000) / 16) (187275663 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2017 / 64000) : ℝ) (2019 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1672992179 / 500000000) (1673097277 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2017 / 64000) (2019 / 64000) (13313251523 / 12500000000) (532563345089 / 500000000000) (1672992179 / 500000000) (1673097277 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2017 / 64000) (2019 / 64000) (1672992179 / 500000000) (1673097277 / 500000000) (43681597 / 1000000000000) (1365911 / 31250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1672992179 / 500000000) (1673097277 / 500000000) (936341411 / 500000000) (187275663 / 100000000) (43681597 / 1000000000000) (1365911 / 31250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0587 :
    ∀ t ∈ Set.Icc ((2019 / 64000) : ℝ) (2021 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1065126690177 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2019 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2019 / 64000)) (1065126690177 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2021 / 64000) : ℝ)) ≤ (1065193262677 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2021 / 64000)) (1065193262677 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((374551251 / 200000000) : ℝ) ≤ Real.exp (3 * (209137093 / 62500000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (209137093 / 62500000) / 16) (374551251 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1673201849 / 500000000) : ℝ) / 16) ≤ (1872830071 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1673201849 / 500000000) / 16) (1872830071 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2019 / 64000) : ℝ) (2021 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (209137093 / 62500000) (1673201849 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2019 / 64000) (2021 / 64000) (1065126690177 / 1000000000000) (1065193262677 / 1000000000000) (209137093 / 62500000) (1673201849 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2019 / 64000) (2021 / 64000) (209137093 / 62500000) (1673201849 / 500000000) (21827099 / 500000000000) (43681737 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (209137093 / 62500000) (1673201849 / 500000000) (374551251 / 200000000) (1872830071 / 1000000000) (21827099 / 500000000000) (43681737 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0588 :
    ∀ t ∈ Set.Icc ((2021 / 64000) : ℝ) (2023 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((266298315669 / 250000000000) : ℝ) ≤ Real.exp (2 * (2021 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2021 / 64000)) (266298315669 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2023 / 64000) : ℝ)) ≤ (133157479917 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2023 / 64000)) (133157479917 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((374565939 / 200000000) : ℝ) ≤ Real.exp (3 * (418300329 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (418300329 / 125000000) / 16) (374565939 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((669322571 / 200000000) : ℝ) / 16) ≤ (1872903519 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (669322571 / 200000000) / 16) (1872903519 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2021 / 64000) : ℝ) (2023 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (418300329 / 125000000) (669322571 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2021 / 64000) (2023 / 64000) (266298315669 / 250000000000) (133157479917 / 125000000000) (418300329 / 125000000) (669322571 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2021 / 64000) (2023 / 64000) (418300329 / 125000000) (669322571 / 200000000) (8725363 / 200000000000) (43654339 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (418300329 / 125000000) (669322571 / 200000000) (374565939 / 200000000) (1872903519 / 1000000000) (8725363 / 200000000000) (43654339 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0589 :
    ∀ t ∈ Set.Icc ((2023 / 64000) : ℝ) (81 / 2560), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((213051967867 / 200000000000) : ℝ) ≤ Real.exp (2 * (2023 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2023 / 64000)) (213051967867 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((81 / 2560) : ℝ)) ≤ (1065326420157 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (81 / 2560)) (1065326420157 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((234112893 / 125000000) : ℝ) ≤ Real.exp (3 * (3346611789 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3346611789 / 1000000000) / 16) (234112893 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((133872881 / 40000000) : ℝ) / 16) ≤ (936488487 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (133872881 / 40000000) / 16) (936488487 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2023 / 64000) : ℝ) (81 / 2560),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3346611789 / 1000000000) (133872881 / 40000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2023 / 64000) (81 / 2560) (213051967867 / 200000000000) (1065326420157 / 1000000000000) (3346611789 / 1000000000) (133872881 / 40000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2023 / 64000) (81 / 2560) (3346611789 / 1000000000) (133872881 / 40000000) (43599447 / 1000000000000) (8725391 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3346611789 / 1000000000) (133872881 / 40000000) (234112893 / 125000000) (936488487 / 500000000) (43599447 / 1000000000000) (8725391 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0590 :
    ∀ t ∈ Set.Icc ((81 / 2560) : ℝ) (2027 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((266331605039 / 250000000000) : ℝ) ≤ Real.exp (2 * (81 / 2560)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (81 / 2560)) (266331605039 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2027 / 64000) : ℝ)) ≤ (1065393005139 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2027 / 64000)) (1065393005139 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1872976599 / 1000000000) : ℝ) ≤ Real.exp (3 * (1673410479 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1673410479 / 500000000) / 16) (1872976599 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((418378901 / 125000000) : ℝ) / 16) ≤ (1873050437 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (418378901 / 125000000) / 16) (1873050437 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((81 / 2560) : ℝ) (2027 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1673410479 / 500000000) (418378901 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (81 / 2560) (2027 / 64000) (266331605039 / 250000000000) (1065393005139 / 1000000000000) (1673410479 / 500000000) (418378901 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (81 / 2560) (2027 / 64000) (1673410479 / 500000000) (418378901 / 125000000) (8714419 / 200000000000) (10899897 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1673410479 / 500000000) (418378901 / 125000000) (1872976599 / 1000000000) (1873050437 / 1000000000) (8714419 / 200000000000) (10899897 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0591 :
    ∀ t ∈ Set.Icc ((2027 / 64000) : ℝ) (2029 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((532696502569 / 500000000000) : ℝ) ≤ Real.exp (2 * (2027 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2027 / 64000)) (532696502569 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2029 / 64000) : ℝ)) ≤ (1065459594283 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2029 / 64000)) (1065459594283 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((936525031 / 500000000) : ℝ) ≤ Real.exp (3 * (3347030141 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3347030141 / 1000000000) / 16) (936525031 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((836810101 / 250000000) : ℝ) / 16) ≤ (468280977 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (836810101 / 250000000) / 16) (468280977 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2027 / 64000) : ℝ) (2029 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3347030141 / 1000000000) (836810101 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2027 / 64000) (2029 / 64000) (532696502569 / 500000000000) (1065459594283 / 1000000000000) (3347030141 / 1000000000) (836810101 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2027 / 64000) (2029 / 64000) (3347030141 / 1000000000) (836810101 / 250000000) (21772379 / 500000000000) (10893059 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3347030141 / 1000000000) (836810101 / 250000000) (936525031 / 500000000) (468280977 / 250000000) (21772379 / 500000000000) (10893059 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0592 :
    ∀ t ∈ Set.Icc ((2029 / 64000) : ℝ) (2031 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((532729797141 / 500000000000) : ℝ) ≤ Real.exp (2 * (2029 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2029 / 64000)) (532729797141 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2031 / 64000) : ℝ)) ≤ (266381546897 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2031 / 64000)) (266381546897 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((468280883 / 250000000) : ℝ) ≤ Real.exp (3 * (3347239337 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3347239337 / 1000000000) / 16) (468280883 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3347449613 / 1000000000) : ℝ) / 16) ≤ (936598693 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3347449613 / 1000000000) / 16) (936598693 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2029 / 64000) : ℝ) (2031 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3347239337 / 1000000000) (3347449613 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2029 / 64000) (2031 / 64000) (532729797141 / 500000000000) (266381546897 / 250000000000) (3347239337 / 1000000000) (3347449613 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2029 / 64000) (2031 / 64000) (3347239337 / 1000000000) (3347449613 / 1000000000) (43517437 / 1000000000000) (43544899 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3347239337 / 1000000000) (3347449613 / 1000000000) (468280883 / 250000000) (936598693 / 500000000) (43517437 / 1000000000000) (43544899 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0593 :
    ∀ t ∈ Set.Icc ((2031 / 64000) : ℝ) (2033 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1065526187587 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2031 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2031 / 64000)) (1065526187587 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2033 / 64000) : ℝ)) ≤ (33299774533 / 31250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2033 / 64000)) (33299774533 / 31250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((187319701 / 100000000) : ℝ) ≤ Real.exp (3 * (1673724273 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1673724273 / 500000000) / 16) (187319701 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((669531767 / 200000000) : ℝ) / 16) ≤ (1873270871 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (669531767 / 200000000) / 16) (1873270871 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2031 / 64000) : ℝ) (2033 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1673724273 / 500000000) (669531767 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2031 / 64000) (2033 / 64000) (1065526187587 / 1000000000000) (33299774533 / 31250000000) (1673724273 / 500000000) (669531767 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2031 / 64000) (2033 / 64000) (1673724273 / 500000000) (669531767 / 200000000) (43490131 / 1000000000000) (43517577 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1673724273 / 500000000) (669531767 / 200000000) (187319701 / 100000000) (1873270871 / 1000000000) (43490131 / 1000000000000) (43517577 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0594 :
    ∀ t ∈ Set.Icc ((2033 / 64000) : ℝ) (407 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((213118557011 / 200000000000) : ℝ) ≤ Real.exp (2 * (2033 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2033 / 64000)) (213118557011 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((407 / 12800) : ℝ)) ≤ (1065659386687 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (407 / 12800)) (1065659386687 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((374654099 / 200000000) : ℝ) ≤ Real.exp (3 * (418457221 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (418457221 / 125000000) / 16) (374654099 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((334786807 / 100000000) : ℝ) / 16) ≤ (468336091 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (334786807 / 100000000) / 16) (468336091 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2033 / 64000) : ℝ) (407 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (418457221 / 125000000) (334786807 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2033 / 64000) (407 / 12800) (213118557011 / 200000000000) (1065659386687 / 1000000000000) (418457221 / 125000000) (334786807 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2033 / 64000) (407 / 12800) (418457221 / 125000000) (334786807 / 100000000) (1086571 / 25000000000) (1359071 / 31250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (418457221 / 125000000) (334786807 / 100000000) (374654099 / 200000000) (468336091 / 250000000) (1086571 / 25000000000) (1359071 / 31250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0595 :
    ∀ t ∈ Set.Icc ((407 / 12800) : ℝ) (2037 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((532829693343 / 500000000000) : ℝ) ≤ Real.exp (2 * (407 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (407 / 12800)) (532829693343 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2037 / 64000) : ℝ)) ≤ (6660787453 / 6250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2037 / 64000)) (6660787453 / 6250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((468335997 / 250000000) : ℝ) ≤ Real.exp (3 * (3347867003 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3347867003 / 1000000000) / 16) (468335997 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1674038659 / 500000000) : ℝ) / 16) ≤ (234177233 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1674038659 / 500000000) / 16) (234177233 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((407 / 12800) : ℝ) (2037 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3347867003 / 1000000000) (1674038659 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (407 / 12800) (2037 / 64000) (532829693343 / 500000000000) (6660787453 / 6250000000) (3347867003 / 1000000000) (1674038659 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (407 / 12800) (2037 / 64000) (3347867003 / 1000000000) (1674038659 / 500000000) (21717783 / 500000000000) (43462981 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3347867003 / 1000000000) (1674038659 / 500000000) (468335997 / 250000000) (234177233 / 125000000) (21717783 / 500000000000) (43462981 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0596 :
    ∀ t ∈ Set.Icc ((2037 / 64000) : ℝ) (2039 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1065725992479 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2037 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2037 / 64000)) (1065725992479 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2039 / 64000) : ℝ)) ≤ (266448150609 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2039 / 64000)) (266448150609 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1873417489 / 1000000000) : ℝ) ≤ Real.exp (3 * (837019063 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (837019063 / 250000000) / 16) (1873417489 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((167414329 / 50000000) : ℝ) / 16) ≤ (468372843 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (167414329 / 50000000) / 16) (468372843 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2037 / 64000) : ℝ) (2039 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (837019063 / 250000000) (167414329 / 50000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2037 / 64000) (2039 / 64000) (1065725992479 / 1000000000000) (266448150609 / 250000000000) (837019063 / 250000000) (167414329 / 50000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2037 / 64000) (2039 / 64000) (837019063 / 250000000) (167414329 / 50000000) (21704153 / 500000000000) (21717853 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (837019063 / 250000000) (167414329 / 50000000) (1873417489 / 1000000000) (468372843 / 250000000) (21704153 / 500000000000) (21717853 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0597 :
    ∀ t ∈ Set.Icc ((2039 / 64000) : ℝ) (2041 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((213158520487 / 200000000000) : ℝ) ≤ Real.exp (2 * (2039 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2039 / 64000)) (213158520487 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2041 / 64000) : ℝ)) ≤ (213171843311 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2041 / 64000)) (213171843311 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((468372749 / 250000000) : ℝ) ≤ Real.exp (3 * (3348285513 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3348285513 / 1000000000) / 16) (468372749 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1674247927 / 500000000) : ℝ) / 16) ≤ (1873564887 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1674247927 / 500000000) / 16) (1873564887 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2039 / 64000) : ℝ) (2041 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3348285513 / 1000000000) (1674247927 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2039 / 64000) (2041 / 64000) (213158520487 / 200000000000) (213171843311 / 200000000000) (3348285513 / 1000000000) (1674247927 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2039 / 64000) (2041 / 64000) (3348285513 / 1000000000) (1674247927 / 500000000) (21690531 / 500000000000) (21704223 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3348285513 / 1000000000) (1674247927 / 500000000) (468372749 / 250000000) (1873564887 / 1000000000) (21690531 / 500000000000) (21704223 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0598 :
    ∀ t ∈ Set.Icc ((2041 / 64000) : ℝ) (2043 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((532929608277 / 500000000000) : ℝ) ≤ Real.exp (2 * (2041 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2041 / 64000)) (532929608277 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2043 / 64000) : ℝ)) ≤ (532962917419 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2043 / 64000)) (532962917419 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1873564511 / 1000000000) : ℝ) ≤ Real.exp (3 * (3348494787 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3348494787 / 1000000000) / 16) (1873564511 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1674352571 / 500000000) : ℝ) / 16) ≤ (187363841 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1674352571 / 500000000) / 16) (187363841 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2041 / 64000) : ℝ) (2043 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3348494787 / 1000000000) (1674352571 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2041 / 64000) (2043 / 64000) (532929608277 / 500000000000) (532962917419 / 500000000000) (3348494787 / 1000000000) (1674352571 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2041 / 64000) (2043 / 64000) (3348494787 / 1000000000) (1674352571 / 500000000) (43353833 / 1000000000000) (21690601 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3348494787 / 1000000000) (1674352571 / 500000000) (1873564511 / 1000000000) (187363841 / 100000000) (43353833 / 1000000000000) (21690601 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0599 :
    ∀ t ∈ Set.Icc ((2043 / 64000) : ℝ) (409 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1065925834837 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2043 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2043 / 64000)) (1065925834837 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((409 / 12800) : ℝ)) ≤ (266498114321 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (409 / 12800)) (266498114321 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((936819017 / 500000000) : ℝ) ≤ Real.exp (3 * (133948163 / 40000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (133948163 / 40000000) / 16) (936819017 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1674457221 / 500000000) : ℝ) / 16) ≤ (93685597 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1674457221 / 500000000) / 16) (93685597 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2043 / 64000) : ℝ) (409 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (133948163 / 40000000) (1674457221 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2043 / 64000) (409 / 12800) (1065925834837 / 1000000000000) (266498114321 / 250000000000) (133948163 / 40000000) (1674457221 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2043 / 64000) (409 / 12800) (133948163 / 40000000) (1674457221 / 500000000) (2166331 / 50000000000) (43353973 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (133948163 / 40000000) (1674457221 / 500000000) (936819017 / 500000000) (93685597 / 50000000) (2166331 / 50000000000) (43353973 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch029 :
    ∀ t ∈ Set.Icc ((401 / 12800) : ℝ) (409 / 12800),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0580
      hpThetaDensityTwoTermCompact_cell0581)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0582
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0583
      hpThetaDensityTwoTermCompact_cell0584)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0585
      hpThetaDensityTwoTermCompact_cell0586)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0587
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0588
      hpThetaDensityTwoTermCompact_cell0589))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0590
      hpThetaDensityTwoTermCompact_cell0591)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0592
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0593
      hpThetaDensityTwoTermCompact_cell0594)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0595
      hpThetaDensityTwoTermCompact_cell0596)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0597
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0598
      hpThetaDensityTwoTermCompact_cell0599)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch029
end HodgeProofHP
