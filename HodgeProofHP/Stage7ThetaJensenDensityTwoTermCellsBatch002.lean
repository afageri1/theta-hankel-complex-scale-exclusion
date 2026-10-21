/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0040 :
    ∀ t ∈ Set.Icc ((13 / 640) : ℝ) (2601 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1041461484251 / 1000000000000) : ℝ) ≤ Real.exp (2 * (13 / 640)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (13 / 640)) (1041461484251 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2601 / 128000) : ℝ)) ≤ (208295551443 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2601 / 128000)) (208295551443 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((369366247 / 200000000) : ℝ) ≤ Real.exp (3 * (3271847067 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3271847067 / 1000000000) / 16) (369366247 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((102246851 / 31250000) : ℝ) / 16) ≤ (18468493 / 10000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (102246851 / 31250000) / 16) (18468493 / 10000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((13 / 640) : ℝ) (2601 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3271847067 / 1000000000) (102246851 / 31250000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (13 / 640) (2601 / 128000) (1041461484251 / 1000000000000) (208295551443 / 200000000000) (3271847067 / 1000000000) (102246851 / 31250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (13 / 640) (2601 / 128000) (3271847067 / 1000000000) (102246851 / 31250000) (54587933 / 1000000000000) (27298239 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3271847067 / 1000000000) (102246851 / 31250000) (369366247 / 200000000) (18468493 / 10000000) (54587933 / 1000000000000) (27298239 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0041 :
    ∀ t ∈ Set.Icc ((2601 / 128000) : ℝ) (1301 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((520738878607 / 500000000000) : ℝ) ≤ Real.exp (2 * (2601 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2601 / 128000)) (520738878607 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1301 / 64000) : ℝ)) ≤ (32546688451 / 31250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1301 / 64000)) (32546688451 / 31250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((923424469 / 500000000) : ℝ) ≤ Real.exp (3 * (327189819 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (327189819 / 100000000) / 16) (923424469 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((817987589 / 250000000) : ℝ) / 16) ≤ (461716751 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (817987589 / 250000000) / 16) (461716751 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2601 / 128000) : ℝ) (1301 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (327189819 / 100000000) (817987589 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2601 / 128000) (1301 / 64000) (520738878607 / 500000000000) (32546688451 / 31250000000) (327189819 / 100000000) (817987589 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2601 / 128000) (1301 / 64000) (327189819 / 100000000) (817987589 / 250000000) (54579561 / 1000000000000) (10917621 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (327189819 / 100000000) (817987589 / 250000000) (923424469 / 500000000) (461716751 / 250000000) (54579561 / 1000000000000) (10917621 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0042 :
    ∀ t ∈ Set.Icc ((1301 / 64000) : ℝ) (2603 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1041494030431 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1301 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1301 / 64000)) (1041494030431 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2603 / 128000) : ℝ)) ≤ (32547196997 / 31250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2603 / 128000)) (32547196997 / 31250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((923433321 / 500000000) : ℝ) ≤ Real.exp (3 * (1635974657 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1635974657 / 500000000) / 16) (923433321 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3272001481 / 1000000000) : ℝ) / 16) ≤ (461721177 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3272001481 / 1000000000) / 16) (461721177 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1301 / 64000) : ℝ) (2603 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1635974657 / 500000000) (3272001481 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1301 / 64000) (2603 / 128000) (1041494030431 / 1000000000000) (32547196997 / 31250000000) (1635974657 / 500000000) (3272001481 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1301 / 64000) (2603 / 128000) (1635974657 / 500000000) (3272001481 / 1000000000) (54571191 / 1000000000000) (54579733 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1635974657 / 500000000) (3272001481 / 1000000000) (923433321 / 500000000) (461721177 / 250000000) (54571191 / 1000000000000) (54579733 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0043 :
    ∀ t ∈ Set.Icc ((2603 / 128000) : ℝ) (651 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1041510303903 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2603 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2603 / 128000)) (1041510303903 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((651 / 32000) : ℝ)) ≤ (1041526577629 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (651 / 32000)) (1041526577629 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((923442173 / 500000000) : ℝ) ≤ Real.exp (3 * (1636000219 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1636000219 / 500000000) / 16) (923442173 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1636026303 / 500000000) : ℝ) / 16) ≤ (461725603 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1636026303 / 500000000) / 16) (461725603 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2603 / 128000) : ℝ) (651 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1636000219 / 500000000) (1636026303 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2603 / 128000) (651 / 32000) (1041510303903 / 1000000000000) (1041526577629 / 1000000000000) (1636000219 / 500000000) (1636026303 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2603 / 128000) (651 / 32000) (1636000219 / 500000000) (1636026303 / 500000000) (27281411 / 500000000000) (54571363 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1636000219 / 500000000) (1636026303 / 500000000) (923442173 / 500000000) (461725603 / 250000000) (27281411 / 500000000000) (54571363 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0044 :
    ∀ t ∈ Set.Icc ((651 / 32000) : ℝ) (521 / 25600), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((260381644407 / 250000000000) : ℝ) ≤ Real.exp (2 * (651 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (651 / 32000)) (260381644407 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((521 / 25600) : ℝ)) ≤ (1041542851609 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (521 / 25600)) (1041542851609 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((36938041 / 20000000) : ℝ) ≤ Real.exp (3 * (818012891 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (818012891 / 250000000) / 16) (36938041 / 20000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((818025933 / 250000000) : ℝ) / 16) ≤ (1846920117 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (818025933 / 250000000) / 16) (1846920117 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((651 / 32000) : ℝ) (521 / 25600),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (818012891 / 250000000) (818025933 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (651 / 32000) (521 / 25600) (260381644407 / 250000000000) (1041542851609 / 1000000000000) (818012891 / 250000000) (818025933 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (651 / 32000) (521 / 25600) (818012891 / 250000000) (818025933 / 250000000) (54554453 / 1000000000000) (27281497 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (818012891 / 250000000) (818025933 / 250000000) (36938041 / 20000000) (1846920117 / 1000000000) (54554453 / 1000000000000) (27281497 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0045 :
    ∀ t ∈ Set.Icc ((521 / 25600) : ℝ) (1303 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((130192856451 / 125000000000) : ℝ) ≤ Real.exp (2 * (521 / 25600)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (521 / 25600)) (130192856451 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1303 / 64000) : ℝ)) ≤ (1041559125843 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1303 / 64000)) (1041559125843 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((369383951 / 200000000) : ℝ) ≤ Real.exp (3 * (327210269 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (327210269 / 100000000) / 16) (369383951 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3272154859 / 1000000000) : ℝ) / 16) ≤ (923468911 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3272154859 / 1000000000) / 16) (923468911 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((521 / 25600) : ℝ) (1303 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (327210269 / 100000000) (3272154859 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (521 / 25600) (1303 / 64000) (130192856451 / 125000000000) (1041559125843 / 1000000000000) (327210269 / 100000000) (3272154859 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (521 / 25600) (1303 / 64000) (327210269 / 100000000) (3272154859 / 1000000000) (27273043 / 500000000000) (436437 / 8000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (327210269 / 100000000) (3272154859 / 1000000000) (369383951 / 200000000) (923468911 / 500000000) (27273043 / 500000000000) (436437 / 8000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0046 :
    ∀ t ∈ Set.Icc ((1303 / 64000) : ℝ) (2607 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((520779562921 / 500000000000) : ℝ) ≤ Real.exp (2 * (1303 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1303 / 64000)) (520779562921 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2607 / 128000) : ℝ)) ≤ (260393850083 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2607 / 128000)) (260393850083 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((92346873 / 50000000) : ℝ) ≤ Real.exp (3 * (3272153817 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3272153817 / 1000000000) / 16) (92346873 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3272205987 / 1000000000) : ℝ) / 16) ≤ (230869441 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3272205987 / 1000000000) / 16) (230869441 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1303 / 64000) : ℝ) (2607 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3272153817 / 1000000000) (3272205987 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1303 / 64000) (2607 / 128000) (520779562921 / 500000000000) (260393850083 / 250000000000) (3272153817 / 1000000000) (3272205987 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1303 / 64000) (2607 / 128000) (3272153817 / 1000000000) (3272205987 / 1000000000) (1363443 / 25000000000) (54546259 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3272153817 / 1000000000) (3272205987 / 1000000000) (92346873 / 50000000) (230869441 / 125000000) (1363443 / 25000000000) (54546259 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0047 :
    ∀ t ∈ Set.Icc ((2607 / 128000) : ℝ) (163 / 8000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1041575400331 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2607 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2607 / 128000)) (1041575400331 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((163 / 8000) : ℝ)) ≤ (41663667003 / 40000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (163 / 8000)) (41663667003 / 40000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((923477583 / 500000000) : ℝ) ≤ Real.exp (3 * (654440989 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (654440989 / 200000000) / 16) (923477583 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((818064279 / 250000000) : ℝ) / 16) ≤ (923486617 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (818064279 / 250000000) / 16) (923486617 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2607 / 128000) : ℝ) (163 / 8000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (654440989 / 200000000) (818064279 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2607 / 128000) (163 / 8000) (1041575400331 / 1000000000000) (41663667003 / 40000000000) (654440989 / 200000000) (818064279 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2607 / 128000) (163 / 8000) (654440989 / 200000000) (818064279 / 250000000) (13632339 / 250000000000) (54537893 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (654440989 / 200000000) (818064279 / 250000000) (923477583 / 500000000) (923486617 / 500000000) (13632339 / 250000000000) (54537893 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0048 :
    ∀ t ∈ Set.Icc ((163 / 8000) : ℝ) (2609 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((520795837537 / 500000000000) : ℝ) ≤ Real.exp (2 * (163 / 8000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (163 / 8000)) (520795837537 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2609 / 128000) : ℝ)) ≤ (130200993759 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2609 / 128000)) (130200993759 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((230871609 / 125000000) : ℝ) ≤ Real.exp (3 * (3272256073 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3272256073 / 1000000000) / 16) (230871609 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((654461649 / 200000000) : ℝ) / 16) ≤ (92349547 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (654461649 / 200000000) / 16) (92349547 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((163 / 8000) : ℝ) (2609 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3272256073 / 1000000000) (654461649 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (163 / 8000) (2609 / 128000) (520795837537 / 500000000000) (130200993759 / 125000000000) (3272256073 / 1000000000) (654461649 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (163 / 8000) (2609 / 128000) (3272256073 / 1000000000) (654461649 / 200000000) (54520993 / 1000000000000) (6816191 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3272256073 / 1000000000) (654461649 / 200000000) (230871609 / 125000000) (92349547 / 50000000) (54520993 / 1000000000000) (6816191 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0049 :
    ∀ t ∈ Set.Icc ((2609 / 128000) : ℝ) (261 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1041607950071 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2609 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2609 / 128000)) (1041607950071 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((261 / 12800) : ℝ)) ≤ (1041624225323 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (261 / 12800)) (1041624225323 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1846990579 / 1000000000) : ℝ) ≤ Real.exp (3 * (3272307203 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3272307203 / 1000000000) / 16) (1846990579 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((209431 / 64000) : ℝ) / 16) ≤ (1847008647 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (209431 / 64000) / 16) (1847008647 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2609 / 128000) : ℝ) (261 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3272307203 / 1000000000) (209431 / 64000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2609 / 128000) (261 / 12800) (1041607950071 / 1000000000000) (1041624225323 / 1000000000000) (3272307203 / 1000000000) (209431 / 64000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2609 / 128000) (261 / 12800) (3272307203 / 1000000000) (209431 / 64000) (5451263 / 100000000000) (13630291 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3272307203 / 1000000000) (209431 / 64000) (1846990579 / 1000000000) (1847008647 / 1000000000) (5451263 / 100000000000) (13630291 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0050 :
    ∀ t ∈ Set.Icc ((261 / 12800) : ℝ) (2611 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((520812112661 / 500000000000) : ℝ) ≤ Real.exp (2 * (261 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (261 / 12800)) (520812112661 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2611 / 128000) : ℝ)) ≤ (1041640500829 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2611 / 128000)) (1041640500829 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((923504143 / 500000000) : ℝ) ≤ Real.exp (3 * (3272358333 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3272358333 / 1000000000) / 16) (923504143 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1636205253 / 500000000) : ℝ) / 16) ≤ (369405271 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1636205253 / 500000000) / 16) (369405271 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((261 / 12800) : ℝ) (2611 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3272358333 / 1000000000) (1636205253 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (261 / 12800) (2611 / 128000) (520812112661 / 500000000000) (1041640500829 / 1000000000000) (3272358333 / 1000000000) (1636205253 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (261 / 12800) (2611 / 128000) (3272358333 / 1000000000) (1636205253 / 500000000) (54504269 / 1000000000000) (27256401 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3272358333 / 1000000000) (1636205253 / 500000000) (923504143 / 500000000) (369405271 / 200000000) (54504269 / 1000000000000) (27256401 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0051 :
    ∀ t ∈ Set.Icc ((2611 / 128000) : ℝ) (653 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((260410125207 / 250000000000) : ℝ) ≤ Real.exp (2 * (2611 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2611 / 128000)) (260410125207 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((653 / 32000) : ℝ)) ≤ (1041656776589 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (653 / 32000)) (1041656776589 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1847025993 / 1000000000) : ℝ) ≤ Real.exp (3 * (409051183 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (409051183 / 125000000) / 16) (1847025993 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1636230819 / 500000000) : ℝ) / 16) ≤ (1847044063 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1636230819 / 500000000) / 16) (1847044063 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2611 / 128000) : ℝ) (653 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (409051183 / 125000000) (1636230819 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2611 / 128000) (653 / 32000) (260410125207 / 250000000000) (1041656776589 / 1000000000000) (409051183 / 125000000) (1636230819 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2611 / 128000) (653 / 32000) (409051183 / 125000000) (1636230819 / 500000000) (54495909 / 1000000000000) (54504441 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (409051183 / 125000000) (1636230819 / 500000000) (1847025993 / 1000000000) (1847044063 / 1000000000) (54495909 / 1000000000000) (54504441 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0052 :
    ∀ t ∈ Set.Icc ((653 / 32000) : ℝ) (2613 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((260414194147 / 250000000000) : ℝ) ≤ Real.exp (2 * (653 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (653 / 32000)) (260414194147 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2613 / 128000) : ℝ)) ≤ (1041673052603 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2613 / 128000)) (1041673052603 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1847043701 / 1000000000) : ℝ) ≤ Real.exp (3 * (818115149 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (818115149 / 250000000) / 16) (1847043701 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3272512771 / 1000000000) : ℝ) / 16) ≤ (1847061771 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3272512771 / 1000000000) / 16) (1847061771 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((653 / 32000) : ℝ) (2613 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (818115149 / 250000000) (3272512771 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (653 / 32000) (2613 / 128000) (260414194147 / 250000000000) (1041673052603 / 1000000000000) (818115149 / 250000000) (3272512771 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (653 / 32000) (2613 / 128000) (818115149 / 250000000) (3272512771 / 1000000000) (1089751 / 20000000000) (54496081 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (818115149 / 250000000) (3272512771 / 1000000000) (1847043701 / 1000000000) (1847061771 / 1000000000) (1089751 / 20000000000) (54496081 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0053 :
    ∀ t ∈ Set.Icc ((2613 / 128000) : ℝ) (1307 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((520836526301 / 500000000000) : ℝ) ≤ Real.exp (2 * (2613 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2613 / 128000)) (520836526301 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1307 / 64000) : ℝ)) ≤ (130211166109 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1307 / 64000)) (130211166109 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1847061409 / 1000000000) : ℝ) ≤ Real.exp (3 * (204531983 / 62500000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (204531983 / 62500000) / 16) (1847061409 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((51133811 / 15625000) : ℝ) / 16) ≤ (46176987 / 25000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (51133811 / 15625000) / 16) (46176987 / 25000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2613 / 128000) : ℝ) (1307 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (204531983 / 62500000) (51133811 / 15625000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2613 / 128000) (1307 / 64000) (520836526301 / 500000000000) (130211166109 / 125000000000) (204531983 / 62500000) (51133811 / 15625000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2613 / 128000) (1307 / 64000) (204531983 / 62500000) (51133811 / 15625000) (6809899 / 125000000000) (27243861 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (204531983 / 62500000) (51133811 / 15625000) (1847061409 / 1000000000) (46176987 / 25000000) (6809899 / 125000000000) (27243861 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0054 :
    ∀ t ∈ Set.Icc ((1307 / 64000) : ℝ) (523 / 25600), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1041689328871 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1307 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1307 / 64000)) (1041689328871 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((523 / 25600) : ℝ)) ≤ (208341121079 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (523 / 25600)) (208341121079 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((923539559 / 500000000) : ℝ) ≤ Real.exp (3 * (1636281431 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1636281431 / 500000000) / 16) (923539559 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1636307519 / 500000000) : ℝ) / 16) ≤ (1847097189 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1636307519 / 500000000) / 16) (1847097189 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1307 / 64000) : ℝ) (523 / 25600),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1636281431 / 500000000) (1636307519 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1307 / 64000) (523 / 25600) (1041689328871 / 1000000000000) (208341121079 / 200000000000) (1636281431 / 500000000) (1636307519 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1307 / 64000) (523 / 25600) (1636281431 / 500000000) (1636307519 / 500000000) (13617709 / 250000000000) (13619841 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1636281431 / 500000000) (1636307519 / 500000000) (923539559 / 500000000) (1847097189 / 1000000000) (13617709 / 250000000000) (13619841 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0055 :
    ∀ t ∈ Set.Icc ((523 / 25600) : ℝ) (327 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((520852802697 / 500000000000) : ℝ) ≤ Real.exp (2 * (523 / 25600)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (523 / 25600)) (520852802697 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((327 / 16000) : ℝ)) ≤ (260430470543 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (327 / 16000)) (260430470543 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1847096827 / 1000000000) : ℝ) ≤ Real.exp (3 * (818153499 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (818153499 / 250000000) / 16) (1847096827 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3272666173 / 1000000000) : ℝ) / 16) ≤ (1847114899 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3272666173 / 1000000000) / 16) (1847114899 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((523 / 25600) : ℝ) (327 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (818153499 / 250000000) (3272666173 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (523 / 25600) (327 / 16000) (520852802697 / 500000000000) (260430470543 / 250000000000) (818153499 / 250000000) (3272666173 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (523 / 25600) (327 / 16000) (818153499 / 250000000) (3272666173 / 1000000000) (680781 / 12500000000) (54471007 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (818153499 / 250000000) (3272666173 / 1000000000) (1847096827 / 1000000000) (1847114899 / 1000000000) (680781 / 12500000000) (54471007 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0056 :
    ∀ t ∈ Set.Icc ((327 / 16000) : ℝ) (2617 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1041721882171 / 1000000000000) : ℝ) ≤ Real.exp (2 * (327 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (327 / 16000)) (1041721882171 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2617 / 128000) : ℝ)) ≤ (1041738159203 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2617 / 128000)) (1041738159203 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1847114537 / 1000000000) : ℝ) ≤ Real.exp (3 * (3272665131 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3272665131 / 1000000000) / 16) (1847114537 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3272717309 / 1000000000) : ℝ) / 16) ≤ (1847132609 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3272717309 / 1000000000) / 16) (1847132609 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((327 / 16000) : ℝ) (2617 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3272665131 / 1000000000) (3272717309 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (327 / 16000) (2617 / 128000) (1041721882171 / 1000000000000) (1041738159203 / 1000000000000) (3272665131 / 1000000000) (3272717309 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (327 / 16000) (2617 / 128000) (3272665131 / 1000000000) (3272717309 / 1000000000) (27227063 / 500000000000) (13615663 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3272665131 / 1000000000) (3272717309 / 1000000000) (1847114537 / 1000000000) (1847132609 / 1000000000) (27227063 / 500000000000) (13615663 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0057 :
    ∀ t ∈ Set.Icc ((2617 / 128000) : ℝ) (1309 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((520869079601 / 500000000000) : ℝ) ≤ Real.exp (2 * (2617 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2617 / 128000)) (520869079601 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1309 / 64000) : ℝ)) ≤ (1041754436489 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1309 / 64000)) (1041754436489 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1847132247 / 1000000000) : ℝ) ≤ Real.exp (3 * (3272716267 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3272716267 / 1000000000) / 16) (1847132247 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1636384223 / 500000000) : ℝ) / 16) ≤ (23089379 / 12500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1636384223 / 500000000) / 16) (23089379 / 12500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2617 / 128000) : ℝ) (1309 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3272716267 / 1000000000) (1636384223 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2617 / 128000) (1309 / 64000) (520869079601 / 500000000000) (1041754436489 / 1000000000000) (3272716267 / 1000000000) (1636384223 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2617 / 128000) (1309 / 64000) (3272716267 / 1000000000) (1636384223 / 500000000) (13611443 / 250000000000) (27227149 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3272716267 / 1000000000) (1636384223 / 500000000) (1847132247 / 1000000000) (23089379 / 12500000) (13611443 / 250000000000) (27227149 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0058 :
    ∀ t ∈ Set.Icc ((1309 / 64000) : ℝ) (2619 / 128000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((130219304561 / 125000000000) : ℝ) ≤ Real.exp (2 * (1309 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1309 / 64000)) (130219304561 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2619 / 128000) : ℝ)) ≤ (104177071403 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2619 / 128000)) (104177071403 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((923574979 / 500000000) : ℝ) ≤ Real.exp (3 * (3272767403 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3272767403 / 1000000000) / 16) (923574979 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3272819583 / 1000000000) : ℝ) / 16) ≤ (1847168031 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3272819583 / 1000000000) / 16) (1847168031 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1309 / 64000) : ℝ) (2619 / 128000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3272767403 / 1000000000) (3272819583 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1309 / 64000) (2619 / 128000) (130219304561 / 125000000000) (104177071403 / 100000000000) (3272767403 / 1000000000) (3272819583 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1309 / 64000) (2619 / 128000) (3272767403 / 1000000000) (3272819583 / 1000000000) (2721871 / 50000000000) (6805743 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3272767403 / 1000000000) (3272819583 / 1000000000) (923574979 / 500000000) (1847168031 / 1000000000) (2721871 / 50000000000) (6805743 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0059 :
    ∀ t ∈ Set.Icc ((2619 / 128000) : ℝ) (131 / 6400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1041770714029 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2619 / 128000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2619 / 128000)) (1041770714029 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((131 / 6400) : ℝ)) ≤ (65111686989 / 62500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (131 / 6400)) (65111686989 / 62500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1847167669 / 1000000000) : ℝ) ≤ Real.exp (3 * (3272818541 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3272818541 / 1000000000) / 16) (1847167669 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1636435361 / 500000000) : ℝ) / 16) ≤ (1847185743 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1636435361 / 500000000) / 16) (1847185743 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2619 / 128000) : ℝ) (131 / 6400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3272818541 / 1000000000) (1636435361 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2619 / 128000) (131 / 6400) (1041770714029 / 1000000000000) (65111686989 / 62500000000) (3272818541 / 1000000000) (1636435361 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2619 / 128000) (131 / 6400) (3272818541 / 1000000000) (1636435361 / 500000000) (54429069 / 1000000000000) (6804699 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3272818541 / 1000000000) (1636435361 / 500000000) (1847167669 / 1000000000) (1847185743 / 1000000000) (54429069 / 1000000000000) (6804699 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch002 :
    ∀ t ∈ Set.Icc ((13 / 640) : ℝ) (131 / 6400),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0040
      hpThetaDensityTwoTermCompact_cell0041)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0042
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0043
      hpThetaDensityTwoTermCompact_cell0044)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0045
      hpThetaDensityTwoTermCompact_cell0046)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0047
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0048
      hpThetaDensityTwoTermCompact_cell0049))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0050
      hpThetaDensityTwoTermCompact_cell0051)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0052
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0053
      hpThetaDensityTwoTermCompact_cell0054)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0055
      hpThetaDensityTwoTermCompact_cell0056)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0057
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0058
      hpThetaDensityTwoTermCompact_cell0059)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch002
end HodgeProofHP
