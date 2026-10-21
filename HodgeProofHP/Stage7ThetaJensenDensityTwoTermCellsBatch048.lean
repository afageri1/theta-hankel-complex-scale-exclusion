/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0960 :
    ∀ t ∈ Set.Icc ((4979 / 64000) : ℝ) (5011 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((584175731941 / 500000000000) : ℝ) ≤ Real.exp (2 * (4979 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4979 / 64000)) (584175731941 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((5011 / 64000) : ℝ)) ≤ (584760199859 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (5011 / 64000)) (584760199859 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1990161273 / 1000000000) : ℝ) ≤ Real.exp (3 * (917620903 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (917620903 / 250000000) / 16) (1990161273 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1837078551 / 500000000) : ℝ) / 16) ≤ (124470783 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1837078551 / 500000000) / 16) (124470783 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4979 / 64000) : ℝ) (5011 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (917620903 / 250000000) (1837078551 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4979 / 64000) (5011 / 64000) (584175731941 / 500000000000) (584760199859 / 500000000000) (917620903 / 250000000) (1837078551 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4979 / 64000) (5011 / 64000) (917620903 / 250000000) (1837078551 / 500000000) (16330577 / 1000000000000) (2063943 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (917620903 / 250000000) (1837078551 / 500000000) (1990161273 / 1000000000) (124470783 / 62500000) (16330577 / 1000000000000) (2063943 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0961 :
    ∀ t ∈ Set.Icc ((5011 / 64000) : ℝ) (5043 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1169520399717 / 1000000000000) : ℝ) ≤ Real.exp (2 * (5011 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (5011 / 64000)) (1169520399717 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((5043 / 64000) : ℝ)) ≤ (1170690505073 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (5043 / 64000)) (1170690505073 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((199153209 / 100000000) : ℝ) ≤ Real.exp (3 * (3674155931 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3674155931 / 1000000000) / 16) (199153209 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((459729137 / 125000000) : ℝ) / 16) ≤ (1992905663 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (459729137 / 125000000) / 16) (1992905663 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((5011 / 64000) : ℝ) (5043 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3674155931 / 1000000000) (459729137 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (5011 / 64000) (5043 / 64000) (1169520399717 / 1000000000000) (1170690505073 / 1000000000000) (3674155931 / 1000000000) (459729137 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (5011 / 64000) (5043 / 64000) (3674155931 / 1000000000) (459729137 / 125000000) (16151473 / 1000000000000) (3266127 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3674155931 / 1000000000) (459729137 / 125000000) (199153209 / 100000000) (1992905663 / 1000000000) (16151473 / 1000000000000) (3266127 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0962 :
    ∀ t ∈ Set.Icc ((5043 / 64000) : ℝ) (203 / 2560), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((73168156567 / 62500000000) : ℝ) ≤ Real.exp (2 * (5043 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (5043 / 64000)) (73168156567 / 62500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((203 / 2560) : ℝ)) ≤ (585930890559 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (203 / 2560)) (585930890559 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((249113153 / 125000000) : ℝ) ≤ Real.exp (3 * (147113277 / 40000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (147113277 / 40000000) / 16) (249113153 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3681512769 / 1000000000) : ℝ) / 16) ≤ (12464257 / 6250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3681512769 / 1000000000) / 16) (12464257 / 6250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((5043 / 64000) : ℝ) (203 / 2560),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (147113277 / 40000000) (3681512769 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (5043 / 64000) (203 / 2560) (73168156567 / 62500000000) (585930890559 / 500000000000) (147113277 / 40000000) (3681512769 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (5043 / 64000) (203 / 2560) (147113277 / 40000000) (3681512769 / 1000000000) (15974157 / 1000000000000) (16151531 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (147113277 / 40000000) (3681512769 / 1000000000) (249113153 / 125000000) (12464257 / 6250000) (15974157 / 1000000000000) (16151531 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0963 :
    ∀ t ∈ Set.Icc ((203 / 2560) : ℝ) (2039 / 25600), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1171861781117 / 1000000000000) : ℝ) ≤ Real.exp (2 * (203 / 2560)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (203 / 2560)) (1171861781117 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2039 / 25600) : ℝ)) ≤ (73292877261 / 62500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2039 / 25600)) (73292877261 / 62500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((49857017 / 25000000) : ℝ) ≤ Real.exp (3 * (920377899 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (920377899 / 250000000) / 16) (49857017 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3684102243 / 1000000000) : ℝ) / 16) ≤ (1995249631 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3684102243 / 1000000000) / 16) (1995249631 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((203 / 2560) : ℝ) (2039 / 25600),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (920377899 / 250000000) (3684102243 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (203 / 2560) (2039 / 25600) (1171861781117 / 1000000000000) (73292877261 / 62500000000) (920377899 / 250000000) (3684102243 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (203 / 2560) (2039 / 25600) (920377899 / 250000000) (3684102243 / 1000000000) (990659 / 62500000000) (7987107 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (920377899 / 250000000) (3684102243 / 1000000000) (49857017 / 25000000) (1995249631 / 1000000000) (990659 / 62500000000) (7987107 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0964 :
    ∀ t ∈ Set.Icc ((2039 / 25600) : ℝ) (2 / 25), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((46907441447 / 40000000000) : ℝ) ≤ Real.exp (2 * (2039 / 25600)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2039 / 25600)) (46907441447 / 40000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2 / 25) : ℝ)) ≤ (73344429437 / 62500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2 / 25)) (73344429437 / 62500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1995249191 / 1000000000) : ℝ) ≤ Real.exp (3 * (3684101069 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3684101069 / 1000000000) / 16) (1995249191 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1843346769 / 500000000) : ℝ) / 16) ≤ (998109647 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1843346769 / 500000000) / 16) (998109647 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2039 / 25600) : ℝ) (2 / 25),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3684101069 / 1000000000) (1843346769 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2039 / 25600) (2 / 25) (46907441447 / 40000000000) (73344429437 / 62500000000) (3684101069 / 1000000000) (1843346769 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2039 / 25600) (2 / 25) (3684101069 / 1000000000) (1843346769 / 500000000) (15727801 / 1000000000000) (79253 / 5000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3684101069 / 1000000000) (1843346769 / 500000000) (1995249191 / 1000000000) (998109647 / 500000000) (15727801 / 1000000000000) (79253 / 5000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch048 :
    ∀ t ∈ Set.Icc ((4979 / 64000) : ℝ) (2 / 25),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0960
      hpThetaDensityTwoTermCompact_cell0961)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0962
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0963
      hpThetaDensityTwoTermCompact_cell0964)))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch048
end HodgeProofHP
