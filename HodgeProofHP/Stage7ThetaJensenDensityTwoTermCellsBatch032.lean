/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0640 :
    ∀ t ∈ Set.Icc ((2143 / 64000) : ℝ) (2147 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1069262063213 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2143 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2143 / 64000)) (1069262063213 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2147 / 64000) : ℝ)) ≤ (42775829173 / 40000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2147 / 64000)) (42775829173 / 40000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1877323729 / 1000000000) : ℝ) ≤ Real.exp (3 * (3359185143 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3359185143 / 1000000000) / 16) (1877323729 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1679803069 / 500000000) : ℝ) / 16) ≤ (75098877 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1679803069 / 500000000) / 16) (75098877 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2143 / 64000) : ℝ) (2147 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3359185143 / 1000000000) (1679803069 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2143 / 64000) (2147 / 64000) (1069262063213 / 1000000000000) (42775829173 / 40000000000) (3359185143 / 1000000000) (1679803069 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2143 / 64000) (2147 / 64000) (3359185143 / 1000000000) (1679803069 / 500000000) (8391793 / 200000000000) (21005997 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3359185143 / 1000000000) (1679803069 / 500000000) (1877323729 / 1000000000) (75098877 / 40000000) (8391793 / 200000000000) (21005997 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0641 :
    ∀ t ∈ Set.Icc ((2147 / 64000) : ℝ) (2151 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((267348932331 / 250000000000) : ℝ) ≤ Real.exp (2 * (2147 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2147 / 64000)) (267348932331 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2151 / 64000) : ℝ)) ≤ (1069529412147 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2151 / 64000)) (1069529412147 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1877471547 / 1000000000) : ℝ) ≤ Real.exp (3 * (839901267 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (839901267 / 250000000) / 16) (1877471547 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((672005223 / 200000000) : ℝ) / 16) ≤ (938809887 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (672005223 / 200000000) / 16) (938809887 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2147 / 64000) : ℝ) (2151 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (839901267 / 250000000) (672005223 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2147 / 64000) (2151 / 64000) (267348932331 / 250000000000) (1069529412147 / 1000000000000) (839901267 / 250000000) (672005223 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2147 / 64000) (2151 / 64000) (839901267 / 250000000) (672005223 / 200000000) (41906133 / 1000000000000) (20979551 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (839901267 / 250000000) (672005223 / 200000000) (1877471547 / 1000000000) (938809887 / 500000000) (41906133 / 1000000000000) (20979551 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0642 :
    ∀ t ∈ Set.Icc ((2151 / 64000) : ℝ) (431 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((534764706073 / 500000000000) : ℝ) ≤ Real.exp (2 * (2151 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2151 / 64000)) (534764706073 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((431 / 12800) : ℝ)) ≤ (1069663111679 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (431 / 12800)) (1069663111679 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((469404849 / 250000000) : ℝ) ≤ Real.exp (3 * (840006261 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (840006261 / 250000000) / 16) (469404849 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((672089229 / 200000000) : ℝ) / 16) ≤ (1877767653 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (672089229 / 200000000) / 16) (1877767653 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2151 / 64000) : ℝ) (431 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (840006261 / 250000000) (672089229 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2151 / 64000) (431 / 12800) (534764706073 / 500000000000) (1069663111679 / 1000000000000) (840006261 / 250000000) (672089229 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2151 / 64000) (431 / 12800) (840006261 / 250000000) (672089229 / 200000000) (41853361 / 1000000000000) (41906269 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (840006261 / 250000000) (672089229 / 200000000) (469404849 / 250000000) (1877767653 / 1000000000) (41853361 / 1000000000000) (41906269 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0643 :
    ∀ t ∈ Set.Icc ((431 / 12800) : ℝ) (2159 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((534831555839 / 500000000000) : ℝ) ≤ Real.exp (2 * (431 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (431 / 12800)) (534831555839 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2159 / 64000) : ℝ)) ≤ (42791873117 / 40000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2159 / 64000)) (42791873117 / 40000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((938883637 / 500000000) : ℝ) ≤ Real.exp (3 * (1680222537 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1680222537 / 500000000) / 16) (938883637 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3360866227 / 1000000000) : ℝ) / 16) ≤ (1877915561 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3360866227 / 1000000000) / 16) (1877915561 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((431 / 12800) : ℝ) (2159 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1680222537 / 500000000) (3360866227 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (431 / 12800) (2159 / 64000) (534831555839 / 500000000000) (42791873117 / 40000000000) (1680222537 / 500000000) (3360866227 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (431 / 12800) (2159 / 64000) (1680222537 / 500000000) (3360866227 / 1000000000) (41800649 / 1000000000000) (41853497 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1680222537 / 500000000) (3360866227 / 1000000000) (938883637 / 500000000) (1877915561 / 1000000000) (41800649 / 1000000000000) (41853497 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0644 :
    ∀ t ∈ Set.Icc ((2159 / 64000) : ℝ) (2163 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((267449206981 / 250000000000) : ℝ) ≤ Real.exp (2 * (2159 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2159 / 64000)) (267449206981 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2163 / 64000) : ℝ)) ≤ (1069930560887 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2163 / 64000)) (1069930560887 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1877915183 / 1000000000) : ℝ) ≤ Real.exp (3 * (840216289 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (840216289 / 250000000) / 16) (1877915183 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3361286361 / 1000000000) : ℝ) / 16) ≤ (3756127 / 2000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3361286361 / 1000000000) / 16) (3756127 / 2000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2159 / 64000) : ℝ) (2163 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (840216289 / 250000000) (3361286361 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2159 / 64000) (2163 / 64000) (267449206981 / 250000000000) (1069930560887 / 1000000000000) (840216289 / 250000000) (3361286361 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2159 / 64000) (2163 / 64000) (840216289 / 250000000) (3361286361 / 1000000000) (10436999 / 250000000000) (8360157 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (840216289 / 250000000) (3361286361 / 1000000000) (1877915183 / 1000000000) (3756127 / 2000000) (10436999 / 250000000000) (8360157 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0645 :
    ∀ t ∈ Set.Icc ((2163 / 64000) : ℝ) (2167 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((534965280443 / 500000000000) : ℝ) ≤ Real.exp (2 * (2163 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2163 / 64000)) (534965280443 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2167 / 64000) : ℝ)) ≤ (535032155283 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2167 / 64000)) (535032155283 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((939031561 / 500000000) : ℝ) ≤ Real.exp (3 * (336128529 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (336128529 / 100000000) / 16) (939031561 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((840426637 / 250000000) : ℝ) / 16) ≤ (187821147 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (840426637 / 250000000) / 16) (187821147 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2163 / 64000) : ℝ) (2167 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (336128529 / 100000000) (840426637 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2163 / 64000) (2167 / 64000) (534965280443 / 500000000000) (535032155283 / 500000000000) (336128529 / 100000000) (840426637 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2163 / 64000) (2167 / 64000) (336128529 / 100000000) (840426637 / 250000000) (41695403 / 1000000000000) (10437033 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (336128529 / 100000000) (840426637 / 250000000) (939031561 / 500000000) (187821147 / 100000000) (41695403 / 1000000000000) (10437033 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0646 :
    ∀ t ∈ Set.Icc ((2167 / 64000) : ℝ) (2171 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((214012862113 / 200000000000) : ℝ) ≤ Real.exp (2 * (2167 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2167 / 64000)) (214012862113 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2171 / 64000) : ℝ)) ≤ (214039615393 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2171 / 64000)) (214039615393 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1878211091 / 1000000000) : ℝ) ≤ Real.exp (3 * (3361705477 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3361705477 / 1000000000) / 16) (1878211091 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((840531697 / 250000000) : ℝ) / 16) ≤ (1878359469 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (840531697 / 250000000) / 16) (1878359469 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2167 / 64000) : ℝ) (2171 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3361705477 / 1000000000) (840531697 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2167 / 64000) (2171 / 64000) (214012862113 / 200000000000) (214039615393 / 200000000000) (3361705477 / 1000000000) (840531697 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2167 / 64000) (2171 / 64000) (3361705477 / 1000000000) (840531697 / 250000000) (41642871 / 1000000000000) (41695539 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3361705477 / 1000000000) (840531697 / 250000000) (1878211091 / 1000000000) (1878359469 / 1000000000) (41642871 / 1000000000000) (41695539 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0647 :
    ∀ t ∈ Set.Icc ((2171 / 64000) : ℝ) (87 / 2560), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((267549519241 / 250000000000) : ℝ) ≤ Real.exp (2 * (2171 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2171 / 64000)) (267549519241 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((87 / 2560) : ℝ)) ≤ (535165930043 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (87 / 2560)) (535165930043 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1878359091 / 1000000000) : ℝ) ≤ Real.exp (3 * (3362125717 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3362125717 / 1000000000) / 16) (1878359091 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((84063677 / 25000000) : ℝ) / 16) ≤ (939253749 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (84063677 / 25000000) / 16) (939253749 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2171 / 64000) : ℝ) (87 / 2560),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3362125717 / 1000000000) (84063677 / 25000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2171 / 64000) (87 / 2560) (267549519241 / 250000000000) (535165930043 / 500000000000) (3362125717 / 1000000000) (84063677 / 25000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2171 / 64000) (87 / 2560) (3362125717 / 1000000000) (84063677 / 25000000) (41590397 / 1000000000000) (20821503 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3362125717 / 1000000000) (84063677 / 25000000) (1878359091 / 1000000000) (939253749 / 500000000) (41590397 / 1000000000000) (20821503 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0648 :
    ∀ t ∈ Set.Icc ((87 / 2560) : ℝ) (2179 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((214066372017 / 200000000000) : ℝ) ≤ Real.exp (2 * (87 / 2560)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (87 / 2560)) (214066372017 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2179 / 64000) : ℝ)) ≤ (1070465659931 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2179 / 64000)) (1070465659931 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((23481339 / 12500000) : ℝ) ≤ Real.exp (3 * (420318251 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (420318251 / 125000000) / 16) (23481339 / 12500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((26273183 / 7812500) : ℝ) / 16) ≤ (939327779 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (26273183 / 7812500) / 16) (939327779 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((87 / 2560) : ℝ) (2179 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (420318251 / 125000000) (26273183 / 7812500) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (87 / 2560) (2179 / 64000) (214066372017 / 200000000000) (1070465659931 / 1000000000000) (420318251 / 125000000) (26273183 / 7812500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (87 / 2560) (2179 / 64000) (420318251 / 125000000) (26273183 / 7812500) (41537983 / 1000000000000) (10397633 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (420318251 / 125000000) (26273183 / 7812500) (23481339 / 12500000) (939327779 / 500000000) (41537983 / 1000000000000) (10397633 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0649 :
    ∀ t ∈ Set.Icc ((2179 / 64000) : ℝ) (2183 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((107046565993 / 100000000000) : ℝ) ≤ Real.exp (2 * (2179 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2179 / 64000)) (107046565993 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2183 / 64000) : ℝ)) ≤ (535299738251 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2183 / 64000)) (535299738251 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((93932759 / 50000000) : ℝ) ≤ Real.exp (3 * (3362966353 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3362966353 / 1000000000) / 16) (93932759 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1681693911 / 500000000) : ℝ) / 16) ≤ (29356307 / 15625000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1681693911 / 500000000) / 16) (29356307 / 15625000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2179 / 64000) : ℝ) (2183 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3362966353 / 1000000000) (1681693911 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2179 / 64000) (2183 / 64000) (107046565993 / 100000000000) (535299738251 / 500000000000) (3362966353 / 1000000000) (1681693911 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2179 / 64000) (2183 / 64000) (3362966353 / 1000000000) (1681693911 / 500000000) (41485629 / 1000000000000) (20769059 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3362966353 / 1000000000) (1681693911 / 500000000) (93932759 / 50000000) (29356307 / 15625000) (41485629 / 1000000000000) (20769059 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0650 :
    ∀ t ∈ Set.Icc ((2183 / 64000) : ℝ) (2187 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1070599476501 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2183 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2183 / 64000)) (1070599476501 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2187 / 64000) : ℝ)) ≤ (1070733309801 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2187 / 64000)) (1070733309801 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1878803269 / 1000000000) : ℝ) ≤ Real.exp (3 * (13453547 / 4000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (13453547 / 4000000) / 16) (1878803269 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3363808271 / 1000000000) : ℝ) / 16) ≤ (234868971 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3363808271 / 1000000000) / 16) (234868971 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2183 / 64000) : ℝ) (2187 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (13453547 / 4000000) (3363808271 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2183 / 64000) (2187 / 64000) (1070599476501 / 1000000000000) (1070733309801 / 1000000000000) (13453547 / 4000000) (3363808271 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2183 / 64000) (2187 / 64000) (13453547 / 4000000) (3363808271 / 1000000000) (20716667 / 500000000000) (10371441 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (13453547 / 4000000) (3363808271 / 1000000000) (1878803269 / 1000000000) (234868971 / 125000000) (20716667 / 500000000000) (10371441 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0651 :
    ∀ t ∈ Set.Icc ((2187 / 64000) : ℝ) (2191 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((5353666549 / 5000000000) : ℝ) ≤ Real.exp (2 * (2187 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2187 / 64000)) (5353666549 / 5000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2191 / 64000) : ℝ)) ≤ (107086715983 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2191 / 64000)) (107086715983 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((187895139 / 100000000) : ℝ) ≤ Real.exp (3 * (4204759 / 1250000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4204759 / 1250000) / 16) (187895139 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1682114387 / 500000000) : ℝ) / 16) ≤ (939549959 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1682114387 / 500000000) / 16) (939549959 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2187 / 64000) : ℝ) (2191 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4204759 / 1250000) (1682114387 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2187 / 64000) (2191 / 64000) (5353666549 / 5000000000) (107086715983 / 100000000000) (4204759 / 1250000) (1682114387 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2187 / 64000) (2191 / 64000) (4204759 / 1250000) (1682114387 / 500000000) (41381099 / 1000000000000) (10358367 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (4204759 / 1250000) (1682114387 / 500000000) (187895139 / 100000000) (939549959 / 500000000) (41381099 / 1000000000000) (10358367 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0652 :
    ∀ t ∈ Set.Icc ((2191 / 64000) : ℝ) (439 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1070867159829 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2191 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2191 / 64000)) (1070867159829 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((439 / 12800) : ℝ)) ≤ (1071001026591 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (439 / 12800)) (1071001026591 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((93954977 / 50000000) : ℝ) ≤ Real.exp (3 * (1682113851 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1682113851 / 500000000) / 16) (93954977 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3364649329 / 1000000000) : ℝ) / 16) ≤ (1879248099 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3364649329 / 1000000000) / 16) (1879248099 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2191 / 64000) : ℝ) (439 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1682113851 / 500000000) (3364649329 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2191 / 64000) (439 / 12800) (1070867159829 / 1000000000000) (1071001026591 / 1000000000000) (1682113851 / 500000000) (3364649329 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2191 / 64000) (439 / 12800) (1682113851 / 500000000) (3364649329 / 1000000000) (20664461 / 500000000000) (41381233 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1682113851 / 500000000) (3364649329 / 1000000000) (93954977 / 50000000) (1879248099 / 1000000000) (20664461 / 500000000000) (41381233 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0653 :
    ∀ t ∈ Set.Icc ((439 / 12800) : ℝ) (2199 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((107100102659 / 100000000000) : ℝ) ≤ Real.exp (2 * (439 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (439 / 12800)) (107100102659 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2199 / 64000) : ℝ)) ≤ (1071134910087 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2199 / 64000)) (1071134910087 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((46981193 / 25000000) : ℝ) ≤ Real.exp (3 * (3364648257 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3364648257 / 1000000000) / 16) (46981193 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((210316871 / 62500000) : ℝ) / 16) ≤ (1879396309 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (210316871 / 62500000) / 16) (1879396309 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((439 / 12800) : ℝ) (2199 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3364648257 / 1000000000) (210316871 / 62500000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (439 / 12800) (2199 / 64000) (107100102659 / 100000000000) (1071134910087 / 1000000000000) (3364648257 / 1000000000) (210316871 / 62500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (439 / 12800) (2199 / 64000) (3364648257 / 1000000000) (210316871 / 62500000) (20638403 / 500000000000) (41329057 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3364648257 / 1000000000) (210316871 / 62500000) (46981193 / 25000000) (1879396309 / 1000000000) (20638403 / 500000000000) (41329057 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0654 :
    ∀ t ∈ Set.Icc ((2199 / 64000) : ℝ) (2203 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((535567455043 / 500000000000) : ℝ) ≤ Real.exp (2 * (2199 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2199 / 64000)) (535567455043 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2203 / 64000) : ℝ)) ≤ (13390860129 / 12500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2203 / 64000)) (13390860129 / 12500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1879395931 / 1000000000) : ℝ) ≤ Real.exp (3 * (52579201 / 15625000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (52579201 / 15625000) / 16) (1879395931 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((841372649 / 250000000) : ℝ) / 16) ≤ (37590891 / 20000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (841372649 / 250000000) / 16) (37590891 / 20000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2199 / 64000) : ℝ) (2203 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (52579201 / 15625000) (841372649 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2199 / 64000) (2203 / 64000) (535567455043 / 500000000000) (13390860129 / 12500000000) (52579201 / 15625000) (841372649 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2199 / 64000) (2203 / 64000) (52579201 / 15625000) (841372649 / 250000000) (10306187 / 250000000000) (2063847 / 50000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (52579201 / 15625000) (841372649 / 250000000) (1879395931 / 1000000000) (37590891 / 20000000) (10306187 / 250000000000) (2063847 / 50000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0655 :
    ∀ t ∈ Set.Icc ((2203 / 64000) : ℝ) (2207 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1071268810319 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2203 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2203 / 64000)) (1071268810319 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2207 / 64000) : ℝ)) ≤ (107140272729 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2207 / 64000)) (107140272729 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((469886043 / 250000000) : ℝ) ≤ Real.exp (3 * (841372381 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (841372381 / 250000000) / 16) (469886043 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3365911309 / 1000000000) : ℝ) / 16) ≤ (939846411 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3365911309 / 1000000000) / 16) (939846411 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2203 / 64000) : ℝ) (2207 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (841372381 / 250000000) (3365911309 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2203 / 64000) (2207 / 64000) (1071268810319 / 1000000000000) (107140272729 / 100000000000) (841372381 / 250000000) (3365911309 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2203 / 64000) (2207 / 64000) (841372381 / 250000000) (3365911309 / 1000000000) (41172749 / 1000000000000) (20612441 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (841372381 / 250000000) (3365911309 / 1000000000) (469886043 / 250000000) (939846411 / 500000000) (41172749 / 1000000000000) (20612441 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0656 :
    ∀ t ∈ Set.Icc ((2207 / 64000) : ℝ) (2211 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1071402727289 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2207 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2207 / 64000)) (1071402727289 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2211 / 64000) : ℝ)) ≤ (535768330501 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2211 / 64000)) (535768330501 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((939846221 / 500000000) : ℝ) ≤ Real.exp (3 * (841477559 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (841477559 / 250000000) / 16) (939846221 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1683166037 / 500000000) : ℝ) / 16) ≤ (1879841123 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1683166037 / 500000000) / 16) (1879841123 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2207 / 64000) : ℝ) (2211 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (841477559 / 250000000) (1683166037 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2207 / 64000) (2211 / 64000) (1071402727289 / 1000000000000) (535768330501 / 500000000000) (841477559 / 250000000) (1683166037 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2207 / 64000) (2211 / 64000) (841477559 / 250000000) (1683166037 / 500000000) (4112081 / 100000000000) (41172883 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (841477559 / 250000000) (1683166037 / 500000000) (939846221 / 500000000) (1879841123 / 1000000000) (4112081 / 100000000000) (41172883 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0657 :
    ∀ t ∈ Set.Icc ((2211 / 64000) : ℝ) (443 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1071536661001 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2211 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2211 / 64000)) (1071536661001 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((443 / 12800) : ℝ)) ≤ (2093106663 / 1953125000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (443 / 12800)) (2093106663 / 1953125000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((234980093 / 125000000) : ℝ) ≤ Real.exp (3 * (3366331001 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3366331001 / 1000000000) / 16) (234980093 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((841688223 / 250000000) : ℝ) / 16) ≤ (939994727 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (841688223 / 250000000) / 16) (939994727 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2211 / 64000) : ℝ) (443 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3366331001 / 1000000000) (841688223 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2211 / 64000) (443 / 12800) (1071536661001 / 1000000000000) (2093106663 / 1953125000) (3366331001 / 1000000000) (841688223 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2211 / 64000) (443 / 12800) (3366331001 / 1000000000) (841688223 / 250000000) (4106893 / 100000000000) (2570059 / 62500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3366331001 / 1000000000) (841688223 / 250000000) (234980093 / 125000000) (939994727 / 500000000) (4106893 / 100000000000) (2570059 / 62500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0658 :
    ∀ t ∈ Set.Icc ((443 / 12800) : ℝ) (2219 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((214334122291 / 200000000000) : ℝ) ≤ Real.exp (2 * (443 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (443 / 12800)) (214334122291 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2219 / 64000) : ℝ)) ≤ (33493893083 / 31250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2219 / 64000)) (33493893083 / 31250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((75199563 / 40000000) : ℝ) ≤ Real.exp (3 * (3366751819 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3366751819 / 1000000000) / 16) (75199563 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1683586881 / 500000000) : ℝ) / 16) ≤ (235017227 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1683586881 / 500000000) / 16) (235017227 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((443 / 12800) : ℝ) (2219 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3366751819 / 1000000000) (1683586881 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (443 / 12800) (2219 / 64000) (214334122291 / 200000000000) (33493893083 / 31250000000) (3366751819 / 1000000000) (1683586881 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (443 / 12800) (2219 / 64000) (3366751819 / 1000000000) (1683586881 / 500000000) (10254277 / 250000000000) (41069063 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3366751819 / 1000000000) (1683586881 / 500000000) (75199563 / 40000000) (235017227 / 125000000) (10254277 / 250000000000) (41069063 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0659 :
    ∀ t ∈ Set.Icc ((2219 / 64000) : ℝ) (2223 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((214360915731 / 200000000000) : ℝ) ≤ Real.exp (2 * (2219 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2219 / 64000)) (214360915731 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2223 / 64000) : ℝ)) ≤ (535969281301 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2223 / 64000)) (535969281301 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1880137437 / 1000000000) : ℝ) ≤ Real.exp (3 * (3367172689 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3367172689 / 1000000000) / 16) (1880137437 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((673518937 / 200000000) : ℝ) / 16) ≤ (3672434 / 1953125) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (673518937 / 200000000) / 16) (3672434 / 1953125) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2219 / 64000) : ℝ) (2223 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3367172689 / 1000000000) (673518937 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2219 / 64000) (2223 / 64000) (214360915731 / 200000000000) (535969281301 / 500000000000) (3367172689 / 1000000000) (673518937 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2219 / 64000) (2223 / 64000) (3367172689 / 1000000000) (673518937 / 200000000) (20482673 / 500000000000) (20508621 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3367172689 / 1000000000) (673518937 / 200000000) (1880137437 / 1000000000) (3672434 / 1953125) (20482673 / 500000000000) (20508621 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch032 :
    ∀ t ∈ Set.Icc ((2143 / 64000) : ℝ) (2223 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0640
      hpThetaDensityTwoTermCompact_cell0641)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0642
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0643
      hpThetaDensityTwoTermCompact_cell0644)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0645
      hpThetaDensityTwoTermCompact_cell0646)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0647
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0648
      hpThetaDensityTwoTermCompact_cell0649))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0650
      hpThetaDensityTwoTermCompact_cell0651)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0652
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0653
      hpThetaDensityTwoTermCompact_cell0654)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0655
      hpThetaDensityTwoTermCompact_cell0656)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0657
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0658
      hpThetaDensityTwoTermCompact_cell0659)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch032
end HodgeProofHP
