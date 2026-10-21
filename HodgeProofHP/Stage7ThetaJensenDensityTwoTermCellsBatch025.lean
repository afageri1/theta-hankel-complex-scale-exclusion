/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0500 :
    ∀ t ∈ Set.Icc ((369 / 12800) : ℝ) (1847 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1059350781283 / 1000000000000) : ℝ) ≤ Real.exp (2 * (369 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (369 / 12800)) (1059350781283 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1847 / 64000) : ℝ)) ≤ (1059416992777 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1847 / 64000)) (1059416992777 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1866395421 / 1000000000) : ℝ) ≤ Real.exp (3 * (3328047939 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3328047939 / 1000000000) / 16) (1866395421 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3328257009 / 1000000000) : ℝ) / 16) ≤ (1866468587 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3328257009 / 1000000000) / 16) (1866468587 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((369 / 12800) : ℝ) (1847 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3328047939 / 1000000000) (3328257009 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (369 / 12800) (1847 / 64000) (1059350781283 / 1000000000000) (1059416992777 / 1000000000000) (3328047939 / 1000000000) (3328257009 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (369 / 12800) (1847 / 64000) (3328047939 / 1000000000) (3328257009 / 1000000000) (9219323 / 200000000000) (23062769 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3328047939 / 1000000000) (3328257009 / 1000000000) (1866395421 / 1000000000) (1866468587 / 1000000000) (9219323 / 200000000000) (23062769 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0501 :
    ∀ t ∈ Set.Icc ((1847 / 64000) : ℝ) (1849 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((132427124097 / 125000000000) : ℝ) ≤ Real.exp (2 * (1847 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1847 / 64000)) (132427124097 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1849 / 64000) : ℝ)) ≤ (132435401051 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1849 / 64000)) (132435401051 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((373293643 / 200000000) : ℝ) ≤ Real.exp (3 * (3328255949 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3328255949 / 1000000000) / 16) (373293643 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((416058129 / 125000000) : ℝ) / 16) ≤ (1866541389 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (416058129 / 125000000) / 16) (1866541389 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1847 / 64000) : ℝ) (1849 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3328255949 / 1000000000) (416058129 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1847 / 64000) (1849 / 64000) (132427124097 / 125000000000) (132435401051 / 125000000000) (3328255949 / 1000000000) (416058129 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1847 / 64000) (1849 / 64000) (3328255949 / 1000000000) (416058129 / 125000000) (2879241 / 62500000000) (46096763 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3328255949 / 1000000000) (416058129 / 125000000) (373293643 / 200000000) (1866541389 / 1000000000) (2879241 / 62500000000) (46096763 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0502 :
    ∀ t ∈ Set.Icc ((1849 / 64000) : ℝ) (1851 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1059483208407 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1849 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1849 / 64000)) (1059483208407 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1851 / 64000) : ℝ)) ≤ (529774714089 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1851 / 64000)) (529774714089 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1866541017 / 1000000000) : ℝ) ≤ Real.exp (3 * (3328463971 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3328463971 / 1000000000) / 16) (1866541017 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3328673067 / 1000000000) : ℝ) / 16) ≤ (933307099 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3328673067 / 1000000000) / 16) (933307099 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1849 / 64000) : ℝ) (1851 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3328463971 / 1000000000) (3328673067 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1849 / 64000) (1851 / 64000) (1059483208407 / 1000000000000) (529774714089 / 500000000000) (3328463971 / 1000000000) (3328673067 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1849 / 64000) (1851 / 64000) (3328463971 / 1000000000) (3328673067 / 1000000000) (23019557 / 500000000000) (11517001 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3328463971 / 1000000000) (3328673067 / 1000000000) (1866541017 / 1000000000) (933307099 / 500000000) (23019557 / 500000000000) (11517001 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0503 :
    ∀ t ∈ Set.Icc ((1851 / 64000) : ℝ) (1853 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1059549428177 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1851 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1851 / 64000)) (1059549428177 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1853 / 64000) : ℝ)) ≤ (1059615652087 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1853 / 64000)) (1059615652087 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((933306913 / 500000000) : ℝ) ≤ Real.exp (3 * (3328672007 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3328672007 / 1000000000) / 16) (933306913 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((832220279 / 250000000) : ℝ) / 16) ≤ (933343507 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (832220279 / 250000000) / 16) (933343507 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1851 / 64000) : ℝ) (1853 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3328672007 / 1000000000) (832220279 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1851 / 64000) (1853 / 64000) (1059549428177 / 1000000000000) (1059615652087 / 1000000000000) (3328672007 / 1000000000) (832220279 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1851 / 64000) (1853 / 64000) (3328672007 / 1000000000) (832220279 / 250000000) (11502597 / 250000000000) (23019631 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3328672007 / 1000000000) (832220279 / 250000000) (933306913 / 500000000) (933343507 / 500000000) (11502597 / 250000000000) (23019631 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0504 :
    ∀ t ∈ Set.Icc ((1853 / 64000) : ℝ) (371 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((529807826043 / 500000000000) : ℝ) ≤ Real.exp (2 * (1853 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1853 / 64000)) (529807826043 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((371 / 12800) : ℝ)) ≤ (211936376027 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (371 / 12800)) (211936376027 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((933343321 / 500000000) : ℝ) ≤ Real.exp (3 * (665776011 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (665776011 / 200000000) / 16) (933343321 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3329089177 / 1000000000) : ℝ) / 16) ≤ (933379919 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3329089177 / 1000000000) / 16) (933379919 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1853 / 64000) : ℝ) (371 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (665776011 / 200000000) (3329089177 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1853 / 64000) (371 / 12800) (529807826043 / 500000000000) (211936376027 / 200000000000) (665776011 / 200000000) (3329089177 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1853 / 64000) (371 / 12800) (665776011 / 200000000) (3329089177 / 1000000000) (22990839 / 500000000000) (5751317 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (665776011 / 200000000) (3329089177 / 1000000000) (933343321 / 500000000) (933379919 / 500000000) (22990839 / 500000000000) (5751317 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0505 :
    ∀ t ∈ Set.Icc ((371 / 12800) : ℝ) (1857 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((529840940067 / 500000000000) : ℝ) ≤ Real.exp (2 * (371 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (371 / 12800)) (529840940067 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1857 / 64000) : ℝ)) ≤ (529874056161 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1857 / 64000)) (529874056161 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((933379733 / 500000000) : ℝ) ≤ Real.exp (3 * (3329088117 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3329088117 / 1000000000) / 16) (933379733 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((832324313 / 250000000) : ℝ) / 16) ≤ (1866832669 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (832324313 / 250000000) / 16) (1866832669 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((371 / 12800) : ℝ) (1857 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3329088117 / 1000000000) (832324313 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (371 / 12800) (1857 / 64000) (529840940067 / 500000000000) (529874056161 / 500000000000) (3329088117 / 1000000000) (832324313 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (371 / 12800) (1857 / 64000) (3329088117 / 1000000000) (832324313 / 250000000) (5744123 / 125000000000) (1839273 / 40000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3329088117 / 1000000000) (832324313 / 250000000) (933379733 / 500000000) (1866832669 / 1000000000) (5744123 / 125000000000) (1839273 / 40000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0506 :
    ∀ t ∈ Set.Icc ((1857 / 64000) : ℝ) (1859 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1059748112321 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1857 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1857 / 64000)) (1059748112321 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1859 / 64000) : ℝ)) ≤ (1059814348649 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1859 / 64000)) (1059814348649 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1866832297 / 1000000000) : ℝ) ≤ Real.exp (3 * (3329296191 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3329296191 / 1000000000) / 16) (1866832297 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((166475267 / 50000000) : ℝ) / 16) ≤ (466726377 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (166475267 / 50000000) / 16) (466726377 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1857 / 64000) : ℝ) (1859 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3329296191 / 1000000000) (166475267 / 50000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1857 / 64000) (1859 / 64000) (1059748112321 / 1000000000000) (1059814348649 / 1000000000000) (3329296191 / 1000000000) (166475267 / 50000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1857 / 64000) (1859 / 64000) (3329296191 / 1000000000) (166475267 / 50000000) (22962153 / 500000000000) (11488283 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3329296191 / 1000000000) (166475267 / 50000000) (1866832297 / 1000000000) (466726377 / 250000000) (22962153 / 500000000000) (11488283 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0507 :
    ∀ t ∈ Set.Icc ((1859 / 64000) : ℝ) (1861 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((132476793581 / 125000000000) : ℝ) ≤ Real.exp (2 * (1859 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1859 / 64000)) (132476793581 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1861 / 64000) : ℝ)) ≤ (264970147279 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1861 / 64000)) (264970147279 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((373381027 / 200000000) : ℝ) ≤ Real.exp (3 * (3329504279 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3329504279 / 1000000000) / 16) (373381027 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((20810709 / 6250000) : ℝ) / 16) ≤ (933489177 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (20810709 / 6250000) / 16) (933489177 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1859 / 64000) : ℝ) (1861 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3329504279 / 1000000000) (20810709 / 6250000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1859 / 64000) (1861 / 64000) (132476793581 / 125000000000) (264970147279 / 250000000000) (3329504279 / 1000000000) (20810709 / 6250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1859 / 64000) (1861 / 64000) (3329504279 / 1000000000) (20810709 / 6250000) (11473911 / 250000000000) (22962227 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3329504279 / 1000000000) (20810709 / 6250000) (373381027 / 200000000) (933489177 / 500000000) (11473911 / 250000000000) (22962227 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0508 :
    ∀ t ∈ Set.Icc ((1861 / 64000) : ℝ) (1863 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((211976117823 / 200000000000) : ℝ) ≤ Real.exp (2 * (1861 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1861 / 64000)) (211976117823 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1863 / 64000) : ℝ)) ≤ (529973416861 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1863 / 64000)) (529973416861 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1866977981 / 1000000000) : ℝ) ≤ Real.exp (3 * (3329712379 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3329712379 / 1000000000) / 16) (1866977981 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1664960777 / 500000000) : ℝ) / 16) ≤ (1867051207 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1664960777 / 500000000) / 16) (1867051207 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1861 / 64000) : ℝ) (1863 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3329712379 / 1000000000) (1664960777 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1861 / 64000) (1863 / 64000) (211976117823 / 200000000000) (529973416861 / 500000000000) (3329712379 / 1000000000) (1664960777 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1861 / 64000) (1863 / 64000) (3329712379 / 1000000000) (1664960777 / 500000000) (45866999 / 1000000000000) (2868487 / 62500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3329712379 / 1000000000) (1664960777 / 500000000) (1866977981 / 1000000000) (1867051207 / 1000000000) (45866999 / 1000000000000) (2868487 / 62500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0509 :
    ∀ t ∈ Set.Icc ((1863 / 64000) : ℝ) (373 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1059946833721 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1863 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1863 / 64000)) (1059946833721 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((373 / 12800) : ℝ)) ≤ (106001308247 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (373 / 12800)) (106001308247 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((373410167 / 200000000) : ℝ) ≤ Real.exp (3 * (3329920493 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3329920493 / 1000000000) / 16) (373410167 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((41626621 / 12500000) : ℝ) / 16) ≤ (466781017 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (41626621 / 12500000) / 16) (466781017 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1863 / 64000) : ℝ) (373 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3329920493 / 1000000000) (41626621 / 12500000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1863 / 64000) (373 / 12800) (1059946833721 / 1000000000000) (106001308247 / 100000000000) (3329920493 / 1000000000) (41626621 / 12500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1863 / 64000) (373 / 12800) (3329920493 / 1000000000) (41626621 / 12500000) (45838369 / 1000000000000) (22933573 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3329920493 / 1000000000) (41626621 / 12500000) (373410167 / 200000000) (466781017 / 250000000) (45838369 / 1000000000000) (22933573 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0510 :
    ∀ t ∈ Set.Icc ((373 / 12800) : ℝ) (1867 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1060013082469 / 1000000000000) : ℝ) ≤ Real.exp (2 * (373 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (373 / 12800)) (1060013082469 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1867 / 64000) : ℝ)) ≤ (530039667679 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1867 / 64000)) (530039667679 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((373424739 / 200000000) : ℝ) ≤ Real.exp (3 * (3330128619 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3330128619 / 1000000000) / 16) (373424739 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((166516891 / 50000000) : ℝ) / 16) ≤ (233399617 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (166516891 / 50000000) / 16) (233399617 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((373 / 12800) : ℝ) (1867 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3330128619 / 1000000000) (166516891 / 50000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (373 / 12800) (1867 / 64000) (1060013082469 / 1000000000000) (530039667679 / 500000000000) (3330128619 / 1000000000) (166516891 / 50000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (373 / 12800) (1867 / 64000) (3330128619 / 1000000000) (166516891 / 50000000) (11452439 / 250000000000) (45838517 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3330128619 / 1000000000) (166516891 / 50000000) (373424739 / 200000000) (233399617 / 125000000) (11452439 / 250000000000) (45838517 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0511 :
    ∀ t ∈ Set.Icc ((1867 / 64000) : ℝ) (1869 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1060079335357 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1867 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1867 / 64000)) (1060079335357 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1869 / 64000) : ℝ)) ≤ (1060145592387 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1869 / 64000)) (1060145592387 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1867196563 / 1000000000) : ℝ) ≤ Real.exp (3 * (3330336759 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3330336759 / 1000000000) / 16) (1867196563 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3330545973 / 1000000000) : ℝ) / 16) ≤ (466817453 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3330545973 / 1000000000) / 16) (466817453 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1867 / 64000) : ℝ) (1869 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3330336759 / 1000000000) (3330545973 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1867 / 64000) (1869 / 64000) (1060079335357 / 1000000000000) (1060145592387 / 1000000000000) (3330336759 / 1000000000) (3330545973 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1867 / 64000) (1869 / 64000) (3330336759 / 1000000000) (3330545973 / 1000000000) (22890579 / 500000000000) (45809903 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3330336759 / 1000000000) (3330545973 / 1000000000) (1867196563 / 1000000000) (466817453 / 250000000) (22890579 / 500000000000) (45809903 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0512 :
    ∀ t ∈ Set.Icc ((1869 / 64000) : ℝ) (1871 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((530072796193 / 500000000000) : ℝ) ≤ Real.exp (2 * (1869 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1869 / 64000)) (530072796193 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1871 / 64000) : ℝ)) ≤ (1060211853557 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1871 / 64000)) (1060211853557 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1867269439 / 1000000000) : ℝ) ≤ Real.exp (3 * (3330544911 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3330544911 / 1000000000) / 16) (1867269439 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1665377069 / 500000000) : ℝ) / 16) ≤ (933671347 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1665377069 / 500000000) / 16) (933671347 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1869 / 64000) : ℝ) (1871 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3330544911 / 1000000000) (1665377069 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1869 / 64000) (1871 / 64000) (530072796193 / 500000000000) (1060211853557 / 1000000000000) (3330544911 / 1000000000) (1665377069 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1869 / 64000) (1871 / 64000) (3330544911 / 1000000000) (1665377069 / 500000000) (22876289 / 500000000000) (22890653 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3330544911 / 1000000000) (1665377069 / 500000000) (1867269439 / 1000000000) (933671347 / 500000000) (22876289 / 500000000000) (22890653 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0513 :
    ∀ t ∈ Set.Icc ((1871 / 64000) : ℝ) (1873 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((265052963389 / 250000000000) : ℝ) ≤ Real.exp (2 * (1871 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1871 / 64000)) (265052963389 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1873 / 64000) : ℝ)) ≤ (1060278118869 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1873 / 64000)) (1060278118869 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((933671161 / 500000000) : ℝ) ≤ Real.exp (3 * (3330753077 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3330753077 / 1000000000) / 16) (933671161 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3330962317 / 1000000000) : ℝ) / 16) ≤ (373483117 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3330962317 / 1000000000) / 16) (373483117 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1871 / 64000) : ℝ) (1873 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3330753077 / 1000000000) (3330962317 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1871 / 64000) (1873 / 64000) (265052963389 / 250000000000) (1060278118869 / 1000000000000) (3330753077 / 1000000000) (3330962317 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1871 / 64000) (1873 / 64000) (3330753077 / 1000000000) (3330962317 / 1000000000) (11431003 / 250000000000) (11438181 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3330753077 / 1000000000) (3330962317 / 1000000000) (933671161 / 500000000) (373483117 / 200000000) (11431003 / 250000000000) (11438181 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0514 :
    ∀ t ∈ Set.Icc ((1873 / 64000) : ℝ) (15 / 512), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((265069529717 / 250000000000) : ℝ) ≤ Real.exp (2 * (1873 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1873 / 64000)) (265069529717 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((15 / 512) : ℝ)) ≤ (530172194161 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (15 / 512)) (530172194161 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((466853803 / 250000000) : ℝ) ≤ Real.exp (3 * (416370157 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (416370157 / 125000000) / 16) (466853803 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((832792627 / 250000000) : ℝ) / 16) ≤ (933744241 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (832792627 / 250000000) / 16) (933744241 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1873 / 64000) : ℝ) (15 / 512),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (416370157 / 125000000) (832792627 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1873 / 64000) (15 / 512) (265069529717 / 250000000000) (530172194161 / 500000000000) (416370157 / 125000000) (832792627 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1873 / 64000) (15 / 512) (416370157 / 125000000) (832792627 / 250000000) (45695463 / 1000000000000) (45724159 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (416370157 / 125000000) (832792627 / 250000000) (466853803 / 250000000) (933744241 / 500000000) (45695463 / 1000000000000) (45724159 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0515 :
    ∀ t ∈ Set.Icc ((15 / 512) : ℝ) (1877 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1060344388321 / 1000000000000) : ℝ) ≤ Real.exp (2 * (15 / 512)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (15 / 512)) (1060344388321 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1877 / 64000) : ℝ)) ≤ (1060410661917 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1877 / 64000)) (1060410661917 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((186748811 / 100000000) : ℝ) ≤ Real.exp (3 * (3331169447 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3331169447 / 1000000000) / 16) (186748811 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3331378713 / 1000000000) : ℝ) / 16) ≤ (1867561387 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3331378713 / 1000000000) / 16) (1867561387 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((15 / 512) : ℝ) (1877 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3331169447 / 1000000000) (3331378713 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (15 / 512) (1877 / 64000) (1060344388321 / 1000000000000) (1060410661917 / 1000000000000) (3331169447 / 1000000000) (3331378713 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (15 / 512) (1877 / 64000) (3331169447 / 1000000000) (3331378713 / 1000000000) (4566693 / 100000000000) (4569561 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3331169447 / 1000000000) (3331378713 / 1000000000) (186748811 / 100000000) (1867561387 / 1000000000) (4566693 / 100000000000) (4569561 / 100000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0516 :
    ∀ t ∈ Set.Icc ((1877 / 64000) : ℝ) (1879 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((265102665479 / 250000000000) : ℝ) ≤ Real.exp (2 * (1877 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1877 / 64000)) (265102665479 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1879 / 64000) : ℝ)) ≤ (212095387931 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1879 / 64000)) (212095387931 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((373512203 / 200000000) : ℝ) ≤ Real.exp (3 * (832844413 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (832844413 / 250000000) / 16) (373512203 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3331586931 / 1000000000) : ℝ) / 16) ≤ (18676343 / 10000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3331586931 / 1000000000) / 16) (18676343 / 10000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1877 / 64000) : ℝ) (1879 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (832844413 / 250000000) (3331586931 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1877 / 64000) (1879 / 64000) (265102665479 / 250000000000) (212095387931 / 200000000000) (832844413 / 250000000) (3331586931 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1877 / 64000) (1879 / 64000) (832844413 / 250000000) (3331586931 / 1000000000) (45638413 / 1000000000000) (45667077 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (832844413 / 250000000) (3331586931 / 1000000000) (373512203 / 200000000) (18676343 / 10000000) (45638413 / 1000000000000) (45667077 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0517 :
    ∀ t ∈ Set.Icc ((1879 / 64000) : ℝ) (1881 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((530238469827 / 500000000000) : ℝ) ≤ Real.exp (2 * (1879 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1879 / 64000)) (530238469827 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1881 / 64000) : ℝ)) ≤ (212108644307 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1881 / 64000)) (212108644307 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1867633927 / 1000000000) : ℝ) ≤ Real.exp (3 * (3331585869 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3331585869 / 1000000000) / 16) (1867633927 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3331795161 / 1000000000) : ℝ) / 16) ≤ (93385361 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3331795161 / 1000000000) / 16) (93385361 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1879 / 64000) : ℝ) (1881 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3331585869 / 1000000000) (3331795161 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1879 / 64000) (1881 / 64000) (530238469827 / 500000000000) (212108644307 / 200000000000) (3331585869 / 1000000000) (3331795161 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1879 / 64000) (1881 / 64000) (3331585869 / 1000000000) (3331795161 / 1000000000) (5701239 / 125000000000) (285241 / 6250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3331585869 / 1000000000) (3331795161 / 1000000000) (1867633927 / 1000000000) (93385361 / 50000000) (5701239 / 125000000000) (285241 / 6250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0518 :
    ∀ t ∈ Set.Icc ((1881 / 64000) : ℝ) (1883 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((530271610767 / 500000000000) : ℝ) ≤ Real.exp (2 * (1881 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1881 / 64000)) (530271610767 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1883 / 64000) : ℝ)) ≤ (530304753779 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1883 / 64000)) (530304753779 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1867706847 / 1000000000) : ℝ) ≤ Real.exp (3 * (33317941 / 10000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (33317941 / 10000000) / 16) (1867706847 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((666400681 / 200000000) : ℝ) / 16) ≤ (1867780147 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (666400681 / 200000000) / 16) (1867780147 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1881 / 64000) : ℝ) (1883 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (33317941 / 10000000) (666400681 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1881 / 64000) (1883 / 64000) (530271610767 / 500000000000) (530304753779 / 500000000000) (33317941 / 10000000) (666400681 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1881 / 64000) (1883 / 64000) (33317941 / 10000000) (666400681 / 200000000) (45581427 / 1000000000000) (45610059 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (33317941 / 10000000) (666400681 / 200000000) (1867706847 / 1000000000) (1867780147 / 1000000000) (45581427 / 1000000000000) (45610059 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0519 :
    ∀ t ∈ Set.Icc ((1883 / 64000) : ℝ) (377 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1060609507557 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1883 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1883 / 64000)) (1060609507557 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((377 / 12800) : ℝ)) ≤ (1060675797723 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (377 / 12800)) (1060675797723 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((74711191 / 40000000) : ℝ) ≤ Real.exp (3 * (416500293 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (416500293 / 125000000) / 16) (74711191 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1666105831 / 500000000) : ℝ) / 16) ≤ (933926541 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1666105831 / 500000000) / 16) (933926541 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1883 / 64000) : ℝ) (377 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (416500293 / 125000000) (1666105831 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1883 / 64000) (377 / 12800) (1060609507557 / 1000000000000) (1060675797723 / 1000000000000) (416500293 / 125000000) (1666105831 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1883 / 64000) (377 / 12800) (416500293 / 125000000) (1666105831 / 500000000) (22776479 / 500000000000) (45581573 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (416500293 / 125000000) (1666105831 / 500000000) (74711191 / 40000000) (933926541 / 500000000) (22776479 / 500000000000) (45581573 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch025 :
    ∀ t ∈ Set.Icc ((369 / 12800) : ℝ) (377 / 12800),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0500
      hpThetaDensityTwoTermCompact_cell0501)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0502
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0503
      hpThetaDensityTwoTermCompact_cell0504)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0505
      hpThetaDensityTwoTermCompact_cell0506)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0507
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0508
      hpThetaDensityTwoTermCompact_cell0509))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0510
      hpThetaDensityTwoTermCompact_cell0511)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0512
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0513
      hpThetaDensityTwoTermCompact_cell0514)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0515
      hpThetaDensityTwoTermCompact_cell0516)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0517
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0518
      hpThetaDensityTwoTermCompact_cell0519)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch025
end HodgeProofHP
