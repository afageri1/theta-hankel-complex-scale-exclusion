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

theorem hpThetaCNV_secondDerivative_cell080 :
    ∀ u : ℝ, u ∈ Set.Icc ((1 / 125) : ℝ) (81 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((203225737 / 200000000) : ℝ) ≤ Real.exp (2 * (1 / 125)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1 / 125)) (203225737 / 200000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((81 / 10000) : ℝ)) ≤ (254082983 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (81 / 10000)) (254082983 / 250000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((2423973 / 100000) : ℝ) ≤ Real.exp ((399021 / 125000) - (81 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((399021 / 125000) - (81 / 10000) / 2) (2423973 / 100000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (1 / 125) (81 / 10000) (203225737 / 200000000) (254082983 / 250000000)
    (399021 / 125000) (3192909 / 1000000) (2423973 / 100000) (8250917 / 200000000) (-2102 / 5) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell081 :
    ∀ u : ℝ, u ∈ Set.Icc ((81 / 10000) : ℝ) (41 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1016331931 / 1000000000) : ℝ) ≤ Real.exp (2 * (81 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (81 / 10000)) (1016331931 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((41 / 5000) : ℝ)) ≤ (1016535219 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41 / 5000)) (1016535219 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((12126991 / 500000) : ℝ) ≤ Real.exp ((1596403 / 500000) - (41 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1596403 / 500000) - (41 / 5000) / 2) (12126991 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (81 / 10000) (41 / 5000) (1016331931 / 1000000000) (1016535219 / 1000000000)
    (1596403 / 500000) (798387 / 250000) (12126991 / 500000) (51537929 / 1250000000) (-52576 / 125) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell082 :
    ∀ u : ℝ, u ∈ Set.Icc ((41 / 5000) : ℝ) (83 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((508267609 / 500000000) : ℝ) ≤ Real.exp (2 * (41 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41 / 5000)) (508267609 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((83 / 10000) : ℝ)) ≤ (508369273 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (83 / 10000)) (508369273 / 500000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((24268267 / 1000000) : ℝ) ≤ Real.exp ((638689 / 200000) - (83 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((638689 / 200000) - (83 / 10000) / 2) (24268267 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (41 / 5000) (83 / 10000) (508267609 / 500000000) (508369273 / 500000000)
    (638689 / 200000) (1597093 / 500000) (24268267 / 1000000) (206030369 / 5000000000) (-52602 / 125) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell083 :
    ∀ u : ℝ, u ∈ Set.Icc ((83 / 10000) : ℝ) (21 / 2500) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((203347709 / 200000000) : ℝ) ≤ Real.exp (2 * (83 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (83 / 10000)) (203347709 / 200000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((21 / 2500) : ℝ)) ≤ (508470957 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (21 / 2500)) (508470957 / 500000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((75883 / 3125) : ℝ) ≤ Real.exp ((798521 / 250000) - (21 / 2500) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((798521 / 250000) - (21 / 2500) / 2) (75883 / 3125) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (83 / 10000) (21 / 2500) (203347709 / 200000000) (508470957 / 500000000)
    (798521 / 250000) (127793 / 40000) (75883 / 3125) (205909097 / 5000000000) (-16841 / 40) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell084 :
    ∀ u : ℝ, u ∈ Set.Icc ((21 / 2500) : ℝ) (17 / 2000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1016941913 / 1000000000) : ℝ) ≤ Real.exp (2 * (21 / 2500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (21 / 2500)) (1016941913 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((17 / 2000) : ℝ)) ≤ (1017145323 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (17 / 2000)) (1017145323 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((12148431 / 500000) : ℝ) ≤ Real.exp ((3194723 / 1000000) - (17 / 2000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3194723 / 1000000) - (17 / 2000) / 2) (12148431 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (21 / 2500) (17 / 2000) (1016941913 / 1000000000) (1017145323 / 1000000000)
    (3194723 / 1000000) (399433 / 125000) (12148431 / 500000) (411575783 / 10000000000) (-421233 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell085 :
    ∀ u : ℝ, u ∈ Set.Icc ((17 / 2000) : ℝ) (43 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((508572661 / 500000000) : ℝ) ≤ Real.exp (2 * (17 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (17 / 2000)) (508572661 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((43 / 5000) : ℝ)) ≤ (254337193 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43 / 5000)) (254337193 / 250000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((24311171 / 1000000) : ℝ) ≤ Real.exp ((1597681 / 500000) - (43 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1597681 / 500000) - (43 / 5000) / 2) (24311171 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (17 / 2000) (43 / 5000) (508572661 / 500000000) (254337193 / 250000000)
    (1597681 / 500000) (3196103 / 1000000) (24311171 / 1000000) (411333539 / 10000000000) (-421441 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell086 :
    ∀ u : ℝ, u ∈ Set.Icc ((43 / 5000) : ℝ) (87 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1017348771 / 1000000000) : ℝ) ≤ Real.exp (2 * (43 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43 / 5000)) (1017348771 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((87 / 10000) : ℝ)) ≤ (508776131 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (87 / 10000)) (508776131 / 500000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((2432549 / 100000) : ℝ) ≤ Real.exp ((3196001 / 1000000) - (87 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3196001 / 1000000) - (87 / 10000) / 2) (2432549 / 100000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (43 / 5000) (87 / 10000) (1017348771 / 1000000000) (508776131 / 500000000)
    (3196001 / 1000000) (3196743 / 1000000) (2432549 / 100000) (411091411 / 10000000000) (-421649 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell087 :
    ∀ u : ℝ, u ∈ Set.Icc ((87 / 10000) : ℝ) (11 / 1250) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1017552261 / 1000000000) : ℝ) ≤ Real.exp (2 * (87 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (87 / 10000)) (1017552261 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((11 / 1250) : ℝ)) ≤ (1017755793 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (11 / 1250)) (1017755793 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((24339817 / 1000000) : ℝ) ≤ Real.exp ((19979 / 6250) - (11 / 1250) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((19979 / 6250) - (11 / 1250) / 2) (24339817 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (87 / 10000) (11 / 1250) (1017552261 / 1000000000) (1017755793 / 1000000000)
    (19979 / 6250) (1598691 / 500000) (24339817 / 1000000) (410849433 / 10000000000) (-421857 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell088 :
    ∀ u : ℝ, u ∈ Set.Icc ((11 / 1250) : ℝ) (89 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((63609737 / 62500000) : ℝ) ≤ Real.exp (2 * (11 / 1250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (11 / 1250)) (63609737 / 62500000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((89 / 10000) : ℝ)) ≤ (203591873 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (89 / 10000)) (203591873 / 200000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((3044269 / 125000) : ℝ) ≤ Real.exp ((3197279 / 1000000) - (89 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3197279 / 1000000) - (89 / 10000) / 2) (3044269 / 125000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (11 / 1250) (89 / 10000) (63609737 / 62500000) (203591873 / 200000000)
    (3197279 / 1000000) (1599011 / 500000) (3044269 / 125000) (102651901 / 2500000000) (-211033 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell089 :
    ∀ u : ℝ, u ∈ Set.Icc ((89 / 10000) : ℝ) (9 / 1000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((254489841 / 250000000) : ℝ) ≤ Real.exp (2 * (89 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (89 / 10000)) (254489841 / 250000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((9 / 1000) : ℝ)) ≤ (1018162977 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9 / 1000)) (1018162977 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((609213 / 25000) : ℝ) ≤ Real.exp ((3197919 / 1000000) - (9 / 1000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3197919 / 1000000) - (9 / 1000) / 2) (609213 / 25000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (89 / 10000) (9 / 1000) (254489841 / 250000000) (1018162977 / 1000000000)
    (3197919 / 1000000) (3198661 / 1000000) (609213 / 25000) (82073101 / 2000000000) (-211137 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cellsBatch008 :
    ∀ u : ℝ, u ∈ Set.Icc ((1 / 125) : ℝ) (9 / 1000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  exact (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell080
      hpThetaCNV_secondDerivative_cell081)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell082
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell083
      hpThetaCNV_secondDerivative_cell084)))
      (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell085
      hpThetaCNV_secondDerivative_cell086)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell087
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell088
      hpThetaCNV_secondDerivative_cell089))))

#print axioms hpThetaCNV_secondDerivative_cellsBatch008
end HodgeProofHP
