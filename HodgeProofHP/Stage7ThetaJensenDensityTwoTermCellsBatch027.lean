/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0540 :
    ∀ t ∈ Set.Icc ((77 / 2560) : ℝ) (1927 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((265500617867 / 250000000000) : ℝ) ≤ Real.exp (2 * (77 / 2560)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (77 / 2560)) (265500617867 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1927 / 64000) : ℝ)) ≤ (531034424349 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1927 / 64000)) (531034424349 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((5841603 / 3125000) : ℝ) ≤ Real.exp (3 * (834094617 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (834094617 / 250000000) / 16) (5841603 / 3125000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3336588061 / 1000000000) : ℝ) / 16) ≤ (233673303 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3336588061 / 1000000000) / 16) (233673303 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((77 / 2560) : ℝ) (1927 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (834094617 / 250000000) (3336588061 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (77 / 2560) (1927 / 64000) (265500617867 / 250000000000) (531034424349 / 500000000000) (834094617 / 250000000) (3336588061 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (77 / 2560) (1927 / 64000) (834094617 / 250000000) (3336588061 / 1000000000) (44958793 / 1000000000000) (44987073 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (834094617 / 250000000) (3336588061 / 1000000000) (5841603 / 3125000) (233673303 / 125000000) (44958793 / 1000000000000) (44987073 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0541 :
    ∀ t ∈ Set.Icc ((1927 / 64000) : ℝ) (1929 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1062068848697 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1927 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1927 / 64000)) (1062068848697 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1929 / 64000) : ℝ)) ≤ (42485409203 / 40000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1929 / 64000)) (42485409203 / 40000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1869386051 / 1000000000) : ℝ) ≤ Real.exp (3 * (1668293499 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1668293499 / 500000000) / 16) (1869386051 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((834199151 / 250000000) : ℝ) / 16) ≤ (934729761 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (834199151 / 250000000) / 16) (934729761 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1927 / 64000) : ℝ) (1929 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1668293499 / 500000000) (834199151 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1927 / 64000) (1929 / 64000) (1062068848697 / 1000000000000) (42485409203 / 40000000000) (1668293499 / 500000000) (834199151 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1927 / 64000) (1929 / 64000) (1668293499 / 500000000) (834199151 / 250000000) (22465337 / 500000000000) (22479469 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1668293499 / 500000000) (834199151 / 250000000) (1869386051 / 1000000000) (934729761 / 500000000) (22465337 / 500000000000) (22479469 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0542 :
    ∀ t ∈ Set.Icc ((1929 / 64000) : ℝ) (1931 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((531067615037 / 500000000000) : ℝ) ≤ Real.exp (2 * (1929 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1929 / 64000)) (531067615037 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1931 / 64000) : ℝ)) ≤ (1062201615601 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1931 / 64000)) (1062201615601 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1869459149 / 1000000000) : ℝ) ≤ Real.exp (3 * (3336795541 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3336795541 / 1000000000) / 16) (1869459149 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3337005161 / 1000000000) : ℝ) / 16) ≤ (467383157 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3337005161 / 1000000000) / 16) (467383157 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1929 / 64000) : ℝ) (1931 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3336795541 / 1000000000) (3337005161 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1929 / 64000) (1931 / 64000) (531067615037 / 500000000000) (1062201615601 / 1000000000000) (3336795541 / 1000000000) (3337005161 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1929 / 64000) (1931 / 64000) (3336795541 / 1000000000) (3337005161 / 1000000000) (44902571 / 1000000000000) (44930819 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3336795541 / 1000000000) (3337005161 / 1000000000) (1869459149 / 1000000000) (467383157 / 250000000) (44902571 / 1000000000000) (44930819 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0543 :
    ∀ t ∈ Set.Icc ((1931 / 64000) : ℝ) (1933 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((2655504039 / 2500000000) : ℝ) ≤ Real.exp (2 * (1931 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1931 / 64000)) (2655504039 / 2500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1933 / 64000) : ℝ)) ≤ (1062268005277 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1933 / 64000)) (1062268005277 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((934766127 / 500000000) : ℝ) ≤ Real.exp (3 * (3337004097 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3337004097 / 1000000000) / 16) (934766127 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((333721373 / 100000000) : ℝ) / 16) ≤ (93480287 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (333721373 / 100000000) / 16) (93480287 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1931 / 64000) : ℝ) (1933 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3337004097 / 1000000000) (333721373 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1931 / 64000) (1933 / 64000) (2655504039 / 2500000000) (1062268005277 / 1000000000000) (3337004097 / 1000000000) (333721373 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1931 / 64000) (1933 / 64000) (3337004097 / 1000000000) (333721373 / 100000000) (11218621 / 250000000000) (11225679 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3337004097 / 1000000000) (333721373 / 100000000) (934766127 / 500000000) (93480287 / 50000000) (11218621 / 250000000000) (11225679 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0544 :
    ∀ t ∈ Set.Icc ((1933 / 64000) : ℝ) (387 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((265567001319 / 250000000000) : ℝ) ≤ Real.exp (2 * (1933 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1933 / 64000)) (265567001319 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((387 / 12800) : ℝ)) ≤ (531167199551 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (387 / 12800)) (531167199551 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1869605367 / 1000000000) : ℝ) ≤ Real.exp (3 * (3337212667 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3337212667 / 1000000000) / 16) (1869605367 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((417177789 / 125000000) : ℝ) / 16) ≤ (1869678861 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (417177789 / 125000000) / 16) (1869678861 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1933 / 64000) : ℝ) (387 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3337212667 / 1000000000) (417177789 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1933 / 64000) (387 / 12800) (265567001319 / 250000000000) (531167199551 / 500000000000) (3337212667 / 1000000000) (417177789 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1933 / 64000) (387 / 12800) (3337212667 / 1000000000) (417177789 / 125000000) (44846413 / 1000000000000) (44874629 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3337212667 / 1000000000) (417177789 / 125000000) (1869605367 / 1000000000) (1869678861 / 1000000000) (44846413 / 1000000000000) (44874629 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0545 :
    ∀ t ∈ Set.Icc ((387 / 12800) : ℝ) (1937 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1062334399101 / 1000000000000) : ℝ) ≤ Real.exp (2 * (387 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (387 / 12800)) (1062334399101 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1937 / 64000) : ℝ)) ≤ (1062400797077 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1937 / 64000)) (1062400797077 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1869678487 / 1000000000) : ℝ) ≤ Real.exp (3 * (3337421249 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3337421249 / 1000000000) / 16) (1869678487 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((834407727 / 250000000) : ℝ) / 16) ≤ (467437997 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (834407727 / 250000000) / 16) (467437997 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((387 / 12800) : ℝ) (1937 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3337421249 / 1000000000) (834407727 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (387 / 12800) (1937 / 64000) (1062334399101 / 1000000000000) (1062400797077 / 1000000000000) (3337421249 / 1000000000) (834407727 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (387 / 12800) (1937 / 64000) (3337421249 / 1000000000) (834407727 / 250000000) (22409179 / 500000000000) (44846557 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3337421249 / 1000000000) (834407727 / 250000000) (1869678487 / 1000000000) (467437997 / 250000000) (22409179 / 500000000000) (44846557 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0546 :
    ∀ t ∈ Set.Icc ((1937 / 64000) : ℝ) (1939 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((265600199269 / 250000000000) : ℝ) ≤ Real.exp (2 * (1937 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1937 / 64000)) (265600199269 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1939 / 64000) : ℝ)) ≤ (531233599601 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1939 / 64000)) (531233599601 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((934875807 / 500000000) : ℝ) ≤ Real.exp (3 * (834407461 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (834407461 / 250000000) / 16) (934875807 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((834459879 / 250000000) : ℝ) / 16) ≤ (1869825123 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (834459879 / 250000000) / 16) (1869825123 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1937 / 64000) : ℝ) (1939 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (834407461 / 250000000) (834459879 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1937 / 64000) (1939 / 64000) (265600199269 / 250000000000) (531233599601 / 500000000000) (834407461 / 250000000) (834459879 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1937 / 64000) (1939 / 64000) (834407461 / 250000000) (834459879 / 250000000) (22395159 / 500000000000) (22409251 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (834407461 / 250000000) (834459879 / 250000000) (934875807 / 500000000) (1869825123 / 1000000000) (22395159 / 500000000000) (22409251 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0547 :
    ∀ t ∈ Set.Icc ((1939 / 64000) : ℝ) (1941 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1062467199201 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1939 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1939 / 64000)) (1062467199201 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1941 / 64000) : ℝ)) ≤ (1062533605477 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1941 / 64000)) (1062533605477 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((7479299 / 4000000) : ℝ) ≤ Real.exp (3 * (3337838453 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3337838453 / 1000000000) / 16) (7479299 / 4000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1669024069 / 500000000) : ℝ) / 16) ≤ (934949133 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1669024069 / 500000000) / 16) (934949133 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1939 / 64000) : ℝ) (1941 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3337838453 / 1000000000) (1669024069 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1939 / 64000) (1941 / 64000) (1062467199201 / 1000000000000) (1062533605477 / 1000000000000) (3337838453 / 1000000000) (1669024069 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1939 / 64000) (1941 / 64000) (3337838453 / 1000000000) (1669024069 / 500000000) (22381147 / 500000000000) (22395231 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3337838453 / 1000000000) (1669024069 / 500000000) (7479299 / 4000000) (934949133 / 500000000) (22381147 / 500000000000) (22395231 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0548 :
    ∀ t ∈ Set.Icc ((1941 / 64000) : ℝ) (1943 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((265633401369 / 250000000000) : ℝ) ≤ Real.exp (2 * (1941 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1941 / 64000)) (265633401369 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1943 / 64000) : ℝ)) ≤ (1062600015903 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1943 / 64000)) (1062600015903 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((467474473 / 250000000) : ℝ) ≤ Real.exp (3 * (1669023537 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1669023537 / 500000000) / 16) (467474473 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((834564193 / 250000000) : ℝ) / 16) ≤ (233746427 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (834564193 / 250000000) / 16) (233746427 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1941 / 64000) : ℝ) (1943 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1669023537 / 500000000) (834564193 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1941 / 64000) (1943 / 64000) (265633401369 / 250000000000) (1062600015903 / 1000000000000) (1669023537 / 500000000) (834564193 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1941 / 64000) (1943 / 64000) (1669023537 / 500000000) (834564193 / 250000000) (22367143 / 500000000000) (22381219 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1669023537 / 500000000) (834564193 / 250000000) (467474473 / 250000000) (233746427 / 125000000) (22367143 / 500000000000) (22381219 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0549 :
    ∀ t ∈ Set.Icc ((1943 / 64000) : ℝ) (389 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((531300007951 / 500000000000) : ℝ) ≤ Real.exp (2 * (1943 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1943 / 64000)) (531300007951 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((389 / 12800) : ℝ)) ≤ (1062666430479 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (389 / 12800)) (1062666430479 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((934985521 / 500000000) : ℝ) ≤ Real.exp (3 * (3338255709 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3338255709 / 1000000000) / 16) (934985521 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((166923271 / 50000000) : ℝ) / 16) ≤ (1870044573 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (166923271 / 50000000) / 16) (1870044573 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1943 / 64000) : ℝ) (389 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3338255709 / 1000000000) (166923271 / 50000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1943 / 64000) (389 / 12800) (531300007951 / 500000000000) (1062666430479 / 1000000000000) (3338255709 / 1000000000) (166923271 / 50000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1943 / 64000) (389 / 12800) (3338255709 / 1000000000) (166923271 / 50000000) (44706293 / 1000000000000) (4473443 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3338255709 / 1000000000) (166923271 / 50000000) (934985521 / 500000000) (1870044573 / 1000000000) (44706293 / 1000000000000) (4473443 / 100000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0550 :
    ∀ t ∈ Set.Icc ((389 / 12800) : ℝ) (1947 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((531333215239 / 500000000000) : ℝ) ≤ Real.exp (2 * (389 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (389 / 12800)) (531333215239 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1947 / 64000) : ℝ)) ≤ (1062732849207 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1947 / 64000)) (1062732849207 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1870044199 / 1000000000) : ℝ) ≤ Real.exp (3 * (834616089 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (834616089 / 250000000) / 16) (1870044199 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((20866713 / 6250000) : ℝ) / 16) ≤ (935058869 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (20866713 / 6250000) / 16) (935058869 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((389 / 12800) : ℝ) (1947 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (834616089 / 250000000) (20866713 / 6250000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (389 / 12800) (1947 / 64000) (531333215239 / 500000000000) (1062732849207 / 1000000000000) (834616089 / 250000000) (20866713 / 6250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (389 / 12800) (1947 / 64000) (834616089 / 250000000) (20866713 / 6250000) (44678317 / 1000000000000) (44706437 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (834616089 / 250000000) (20866713 / 6250000) (1870044199 / 1000000000) (935058869 / 500000000) (44678317 / 1000000000000) (44706437 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0551 :
    ∀ t ∈ Set.Icc ((1947 / 64000) : ℝ) (1949 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((531366424603 / 500000000000) : ℝ) ≤ Real.exp (2 * (1947 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1947 / 64000)) (531366424603 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1949 / 64000) : ℝ)) ≤ (212559854417 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1949 / 64000)) (212559854417 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((467529341 / 250000000) : ℝ) ≤ Real.exp (3 * (3338673017 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3338673017 / 1000000000) / 16) (467529341 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1669441377 / 500000000) : ℝ) / 16) ≤ (187019091 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1669441377 / 500000000) / 16) (187019091 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1947 / 64000) : ℝ) (1949 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3338673017 / 1000000000) (1669441377 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1947 / 64000) (1949 / 64000) (531366424603 / 500000000000) (212559854417 / 200000000000) (3338673017 / 1000000000) (1669441377 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1947 / 64000) (1949 / 64000) (3338673017 / 1000000000) (1669441377 / 500000000) (11162589 / 250000000000) (44678461 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3338673017 / 1000000000) (1669441377 / 500000000) (467529341 / 250000000) (187019091 / 100000000) (11162589 / 250000000000) (44678461 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0552 :
    ∀ t ∈ Set.Icc ((1949 / 64000) : ℝ) (1951 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((265699818021 / 250000000000) : ℝ) ≤ Real.exp (2 * (1949 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1949 / 64000)) (265699818021 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1951 / 64000) : ℝ)) ≤ (265716424779 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1951 / 64000)) (265716424779 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((233773817 / 125000000) : ℝ) ≤ Real.exp (3 * (333888169 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (333888169 / 100000000) / 16) (233773817 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3339091441 / 1000000000) : ℝ) / 16) ≤ (187026409 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3339091441 / 1000000000) / 16) (187026409 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1949 / 64000) : ℝ) (1951 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (333888169 / 100000000) (3339091441 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1949 / 64000) (1951 / 64000) (265699818021 / 250000000000) (265716424779 / 250000000000) (333888169 / 100000000) (3339091441 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1949 / 64000) (1951 / 64000) (333888169 / 100000000) (3339091441 / 1000000000) (44622411 / 1000000000000) (89301 / 2000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (333888169 / 100000000) (3339091441 / 1000000000) (233773817 / 125000000) (187026409 / 100000000) (44622411 / 1000000000000) (89301 / 2000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0553 :
    ∀ t ∈ Set.Icc ((1951 / 64000) : ℝ) (1953 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((212573139823 / 200000000000) : ℝ) ≤ Real.exp (2 * (1951 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1951 / 64000)) (212573139823 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1953 / 64000) : ℝ)) ≤ (531466065149 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1953 / 64000)) (531466065149 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((467565929 / 250000000) : ℝ) ≤ Real.exp (3 * (3339090377 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3339090377 / 1000000000) / 16) (467565929 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3339300141 / 1000000000) : ℝ) / 16) ≤ (1870337277 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3339300141 / 1000000000) / 16) (1870337277 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1951 / 64000) : ℝ) (1953 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3339090377 / 1000000000) (3339300141 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1951 / 64000) (1953 / 64000) (212573139823 / 200000000000) (531466065149 / 500000000000) (3339090377 / 1000000000) (3339300141 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1951 / 64000) (1953 / 64000) (3339090377 / 1000000000) (3339300141 / 1000000000) (22297241 / 500000000000) (8924511 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3339090377 / 1000000000) (3339300141 / 1000000000) (467565929 / 250000000) (1870337277 / 1000000000) (22297241 / 500000000000) (8924511 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0554 :
    ∀ t ∈ Set.Icc ((1953 / 64000) : ℝ) (391 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1062932130297 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1953 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1953 / 64000)) (1062932130297 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((391 / 12800) : ℝ)) ≤ (4152338147 / 3906250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (391 / 12800)) (4152338147 / 3906250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1870336903 / 1000000000) : ℝ) ≤ Real.exp (3 * (3339299077 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3339299077 / 1000000000) / 16) (1870336903 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3339508853 / 1000000000) : ℝ) / 16) ≤ (1870410471 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3339508853 / 1000000000) / 16) (1870410471 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1953 / 64000) : ℝ) (391 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3339299077 / 1000000000) (3339508853 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1953 / 64000) (391 / 12800) (1062932130297 / 1000000000000) (4152338147 / 3906250000) (3339299077 / 1000000000) (3339508853 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1953 / 64000) (391 / 12800) (3339299077 / 1000000000) (3339508853 / 1000000000) (5570821 / 125000000000) (356757 / 8000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3339299077 / 1000000000) (3339508853 / 1000000000) (1870336903 / 1000000000) (1870410471 / 1000000000) (5570821 / 125000000000) (356757 / 8000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0555 :
    ∀ t ∈ Set.Icc ((391 / 12800) : ℝ) (1957 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1062998565631 / 1000000000000) : ℝ) ≤ Real.exp (2 * (391 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (391 / 12800)) (1062998565631 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1957 / 64000) : ℝ)) ≤ (1063065005119 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1957 / 64000)) (1063065005119 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1870410097 / 1000000000) : ℝ) ≤ Real.exp (3 * (3339507789 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3339507789 / 1000000000) / 16) (1870410097 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3339717579 / 1000000000) : ℝ) / 16) ≤ (1870483673 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3339717579 / 1000000000) / 16) (1870483673 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((391 / 12800) : ℝ) (1957 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3339507789 / 1000000000) (3339717579 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (391 / 12800) (1957 / 64000) (1062998565631 / 1000000000000) (1063065005119 / 1000000000000) (3339507789 / 1000000000) (3339717579 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (391 / 12800) (1957 / 64000) (3339507789 / 1000000000) (3339717579 / 1000000000) (4453867 / 100000000000) (5570839 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3339507789 / 1000000000) (3339717579 / 1000000000) (1870410097 / 1000000000) (1870483673 / 1000000000) (4453867 / 100000000000) (5570839 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0556 :
    ∀ t ∈ Set.Icc ((1957 / 64000) : ℝ) (1959 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((531532502559 / 500000000000) : ℝ) ≤ Real.exp (2 * (1957 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1957 / 64000)) (531532502559 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1959 / 64000) : ℝ)) ≤ (531565724379 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1959 / 64000)) (531565724379 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1870483299 / 1000000000) : ℝ) ≤ Real.exp (3 * (667943303 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (667943303 / 200000000) / 16) (1870483299 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1669963159 / 500000000) : ℝ) / 16) ≤ (1870556883 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1669963159 / 500000000) / 16) (1870556883 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1957 / 64000) : ℝ) (1959 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (667943303 / 200000000) (1669963159 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1957 / 64000) (1959 / 64000) (531532502559 / 500000000000) (531565724379 / 500000000000) (667943303 / 200000000) (1669963159 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1957 / 64000) (1959 / 64000) (667943303 / 200000000) (1669963159 / 500000000) (11127697 / 250000000000) (22269407 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (667943303 / 200000000) (1669963159 / 500000000) (1870483299 / 1000000000) (1870556883 / 1000000000) (11127697 / 250000000000) (22269407 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0557 :
    ∀ t ∈ Set.Icc ((1959 / 64000) : ℝ) (1961 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1063131448757 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1959 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1959 / 64000)) (1063131448757 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1961 / 64000) : ℝ)) ≤ (21263957931 / 20000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1961 / 64000)) (21263957931 / 20000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1870556509 / 1000000000) : ℝ) ≤ Real.exp (3 * (1669962627 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1669962627 / 500000000) / 16) (1870556509 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((334013507 / 100000000) : ℝ) / 16) ≤ (18706301 / 10000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (334013507 / 100000000) / 16) (18706301 / 10000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1959 / 64000) : ℝ) (1961 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1669962627 / 500000000) (334013507 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1959 / 64000) (1961 / 64000) (1063131448757 / 1000000000000) (21263957931 / 20000000000) (1669962627 / 500000000) (334013507 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1959 / 64000) (1961 / 64000) (1669962627 / 500000000) (334013507 / 100000000) (22241461 / 500000000000) (44510931 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1669962627 / 500000000) (334013507 / 100000000) (1870556509 / 1000000000) (18706301 / 10000000) (22241461 / 500000000000) (44510931 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0558 :
    ∀ t ∈ Set.Icc ((1961 / 64000) : ℝ) (1963 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1063197896549 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1961 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1961 / 64000)) (1063197896549 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1963 / 64000) : ℝ)) ≤ (212652869699 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1963 / 64000)) (212652869699 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((935314863 / 500000000) : ℝ) ≤ Real.exp (3 * (1670067003 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1670067003 / 500000000) / 16) (935314863 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((668068767 / 200000000) : ℝ) / 16) ≤ (467675831 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (668068767 / 200000000) / 16) (467675831 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1961 / 64000) : ℝ) (1963 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1670067003 / 500000000) (668068767 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1961 / 64000) (1963 / 64000) (1063197896549 / 1000000000000) (212652869699 / 200000000000) (1670067003 / 500000000) (668068767 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1961 / 64000) (1963 / 64000) (1670067003 / 500000000) (668068767 / 200000000) (44455071 / 1000000000000) (8896613 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1670067003 / 500000000) (668068767 / 200000000) (935314863 / 500000000) (467675831 / 250000000) (44455071 / 1000000000000) (8896613 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0559 :
    ∀ t ∈ Set.Icc ((1963 / 64000) : ℝ) (393 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((531632174247 / 500000000000) : ℝ) ≤ Real.exp (2 * (1963 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1963 / 64000)) (531632174247 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((393 / 12800) : ℝ)) ≤ (1063330804593 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (393 / 12800)) (1063330804593 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((37414059 / 20000000) : ℝ) ≤ Real.exp (3 * (3340342771 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3340342771 / 1000000000) / 16) (37414059 / 20000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3340552613 / 1000000000) : ℝ) / 16) ≤ (467694139 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3340552613 / 1000000000) / 16) (467694139 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1963 / 64000) : ℝ) (393 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3340342771 / 1000000000) (3340552613 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1963 / 64000) (393 / 12800) (531632174247 / 500000000000) (1063330804593 / 1000000000000) (3340342771 / 1000000000) (3340552613 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1963 / 64000) (393 / 12800) (3340342771 / 1000000000) (3340552613 / 1000000000) (11106809 / 250000000000) (22227607 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3340342771 / 1000000000) (3340552613 / 1000000000) (37414059 / 20000000) (467694139 / 250000000) (11106809 / 250000000000) (22227607 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch027 :
    ∀ t ∈ Set.Icc ((77 / 2560) : ℝ) (393 / 12800),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0540
      hpThetaDensityTwoTermCompact_cell0541)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0542
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0543
      hpThetaDensityTwoTermCompact_cell0544)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0545
      hpThetaDensityTwoTermCompact_cell0546)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0547
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0548
      hpThetaDensityTwoTermCompact_cell0549))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0550
      hpThetaDensityTwoTermCompact_cell0551)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0552
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0553
      hpThetaDensityTwoTermCompact_cell0554)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0555
      hpThetaDensityTwoTermCompact_cell0556)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0557
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0558
      hpThetaDensityTwoTermCompact_cell0559)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch027
end HodgeProofHP
