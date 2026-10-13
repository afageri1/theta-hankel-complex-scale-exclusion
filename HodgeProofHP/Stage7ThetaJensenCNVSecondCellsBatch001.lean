/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCNVIntervalGluing

/-! Ten exact rational cells. All arithmetic is checked by Lean's kernel. -/
set_option maxHeartbeats 2000000
noncomputable section
namespace HodgeProofHP

theorem hpThetaCNV_secondDerivative_cell010 :
    ∀ u : ℝ, u ∈ Set.Icc ((1 / 1000) : ℝ) (11 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1002002001 / 1000000000) : ℝ) ≤ Real.exp (2 * (1 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1 / 1000)) (1002002001 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((11 / 10000) : ℝ)) ≤ (501101211 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (11 / 10000)) (501101211 / 500000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((11634569 / 500000) : ℝ) ≤ Real.exp ((3147789 / 1000000) - (11 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3147789 / 1000000) - (11 / 10000) / 2) (11634569 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (1 / 1000) (11 / 10000) (1002002001 / 1000000000) (501101211 / 500000000)
    (3147789 / 1000000) (78713 / 25000) (11634569 / 500000) (21487689 / 500000000) (-405793 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell011 :
    ∀ u : ℝ, u ∈ Set.Icc ((11 / 10000) : ℝ) (3 / 2500) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1002202421 / 1000000000) : ℝ) ≤ Real.exp (2 * (11 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (11 / 10000)) (1002202421 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((3 / 2500) : ℝ)) ≤ (1002402883 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3 / 2500)) (1002402883 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((2328261 / 100000) : ℝ) ≤ Real.exp ((1574209 / 500000) - (3 / 2500) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1574209 / 500000) - (3 / 2500) / 2) (2328261 / 100000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (11 / 10000) (3 / 2500) (1002202421 / 1000000000) (1002402883 / 1000000000)
    (1574209 / 500000) (3149149 / 1000000) (2328261 / 100000) (53688139 / 1250000000) (-203001 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell012 :
    ∀ u : ℝ, u ∈ Set.Icc ((3 / 2500) : ℝ) (13 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((501201441 / 500000000) : ℝ) ≤ Real.exp (2 * (3 / 2500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3 / 2500)) (501201441 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((13 / 10000) : ℝ)) ≤ (1002603383 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (13 / 10000)) (1002603383 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((11648057 / 500000) : ℝ) ≤ Real.exp ((393631 / 125000) - (13 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((393631 / 125000) - (13 / 10000) / 2) (11648057 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (3 / 2500) (13 / 10000) (501201441 / 500000000) (1002603383 / 1000000000)
    (393631 / 125000) (3149779 / 1000000) (11648057 / 500000) (214628071 / 5000000000) (-406211 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell013 :
    ∀ u : ℝ, u ∈ Set.Icc ((13 / 10000) : ℝ) (7 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((501301691 / 500000000) : ℝ) ≤ Real.exp (2 * (13 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (13 / 10000)) (501301691 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((7 / 5000) : ℝ)) ≤ (250700981 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (7 / 5000)) (250700981 / 250000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((186477 / 8000) : ℝ) ≤ Real.exp ((1574839 / 500000) - (7 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1574839 / 500000) - (7 / 5000) / 2) (186477 / 8000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (13 / 10000) (7 / 5000) (501301691 / 500000000) (250700981 / 250000000)
    (1574839 / 500000) (3150409 / 1000000) (186477 / 8000) (429007331 / 10000000000) (-20321 / 50) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell014 :
    ∀ u : ℝ, u ∈ Set.Icc ((7 / 5000) : ℝ) (3 / 2000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1002803923 / 1000000000) : ℝ) ≤ Real.exp (2 * (7 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (7 / 5000)) (1002803923 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((3 / 2000) : ℝ)) ≤ (200600901 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3 / 2000)) (200600901 / 200000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((2915393 / 125000) : ℝ) ≤ Real.exp ((787577 / 250000) - (3 / 2000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((787577 / 250000) - (3 / 2000) / 2) (2915393 / 125000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (7 / 5000) (3 / 2000) (1002803923 / 1000000000) (200600901 / 200000000)
    (787577 / 250000) (3151039 / 1000000) (2915393 / 125000) (214379331 / 5000000000) (-101657 / 250) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell015 :
    ∀ u : ℝ, u ∈ Set.Icc ((3 / 2000) : ℝ) (1 / 625) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((125375563 / 125000000) : ℝ) ≤ Real.exp (2 * (3 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3 / 2000)) (125375563 / 125000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((1 / 625) : ℝ)) ≤ (501602563 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1 / 625)) (501602563 / 500000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((23336671 / 1000000) : ℝ) ≤ Real.exp ((1575469 / 500000) - (1 / 625) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1575469 / 500000) - (1 / 625) / 2) (23336671 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (3 / 2000) (1 / 625) (125375563 / 125000000) (501602563 / 500000000)
    (1575469 / 500000) (315167 / 100000) (23336671 / 1000000) (214255067 / 5000000000) (-203419 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell016 :
    ∀ u : ℝ, u ∈ Set.Icc ((1 / 625) : ℝ) (17 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((8025641 / 8000000) : ℝ) ≤ Real.exp (2 * (1 / 625)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1 / 625)) (8025641 / 8000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((17 / 10000) : ℝ)) ≤ (1003405787 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (17 / 10000)) (1003405787 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((11675103 / 500000) : ℝ) ≤ Real.exp ((196973 / 62500) - (17 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((196973 / 62500) - (17 / 10000) / 2) (11675103 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (1 / 625) (17 / 10000) (8025641 / 8000000) (1003405787 / 1000000000)
    (196973 / 62500) (31523 / 10000) (11675103 / 500000) (428261747 / 10000000000) (-203523 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell017 :
    ∀ u : ℝ, u ∈ Set.Icc ((17 / 10000) : ℝ) (9 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((501702893 / 500000000) : ℝ) ≤ Real.exp (2 * (17 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (17 / 10000)) (501702893 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((9 / 5000) : ℝ)) ≤ (125450811 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9 / 5000)) (125450811 / 125000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((5840943 / 250000) : ℝ) ≤ Real.exp ((3152199 / 1000000) - (9 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3152199 / 1000000) - (9 / 5000) / 2) (5840943 / 250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (17 / 10000) (9 / 5000) (501702893 / 500000000) (125450811 / 125000000)
    (3152199 / 1000000) (3152931 / 1000000) (5840943 / 250000) (10700327 / 250000000) (-50907 / 125) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell018 :
    ∀ u : ℝ, u ∈ Set.Icc ((9 / 5000) : ℝ) (19 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1003606487 / 1000000000) : ℝ) ≤ Real.exp (2 * (9 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9 / 5000)) (1003606487 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((19 / 10000) : ℝ)) ≤ (100380723 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (19 / 10000)) (100380723 / 100000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((11688661 / 500000) : ℝ) ≤ Real.exp ((3152829 / 1000000) - (19 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3152829 / 1000000) - (19 / 10000) / 2) (11688661 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (9 / 5000) (19 / 10000) (1003606487 / 1000000000) (100380723 / 100000000)
    (3152829 / 1000000) (3153561 / 1000000) (11688661 / 500000) (213882497 / 5000000000) (-50933 / 125) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell019 :
    ∀ u : ℝ, u ∈ Set.Icc ((19 / 10000) : ℝ) (1 / 500) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1003807229 / 1000000000) : ℝ) ≤ Real.exp (2 * (19 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (19 / 10000)) (1003807229 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((1 / 500) : ℝ)) ≤ (1004008011 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1 / 500)) (1004008011 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((2923863 / 125000) : ℝ) ≤ Real.exp ((157673 / 50000) - (1 / 500) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((157673 / 50000) - (1 / 500) / 2) (2923863 / 125000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (19 / 10000) (1 / 500) (1003807229 / 1000000000) (1004008011 / 1000000000)
    (157673 / 50000) (197137 / 62500) (2923863 / 125000) (427516611 / 10000000000) (-407673 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cellsBatch001 :
    ∀ u : ℝ, u ∈ Set.Icc ((1 / 1000) : ℝ) (1 / 500) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  exact (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell010
      hpThetaCNV_secondDerivative_cell011)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell012
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell013
      hpThetaCNV_secondDerivative_cell014)))
      (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell015
      hpThetaCNV_secondDerivative_cell016)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell017
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell018
      hpThetaCNV_secondDerivative_cell019))))

#print axioms hpThetaCNV_secondDerivative_cellsBatch001
end HodgeProofHP
