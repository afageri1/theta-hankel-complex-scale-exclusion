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

theorem hpThetaCNV_secondDerivative_cell180 :
    ∀ u : ℝ, u ∈ Set.Icc ((9 / 500) : ℝ) (181 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((518327923 / 500000000) : ℝ) ≤ Real.exp (2 * (9 / 500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9 / 500)) (518327923 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((181 / 10000) : ℝ)) ≤ (1036863199 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (181 / 10000)) (1036863199 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25724817 / 1000000) : ℝ) ≤ Real.exp ((1628327 / 500000) - (181 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1628327 / 500000) - (181 / 10000) / 2) (25724817 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (9 / 500) (181 / 10000) (518327923 / 500000000) (1036863199 / 1000000000)
    (1628327 / 500000) (325741 / 100000) (25724817 / 1000000) (77745937 / 2000000000) (-110279 / 250) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell181 :
    ∀ u : ℝ, u ∈ Set.Icc ((181 / 10000) : ℝ) (91 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((518431599 / 500000000) : ℝ) ≤ Real.exp (2 * (181 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (181 / 10000)) (518431599 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((91 / 5000) : ℝ)) ≤ (4051057 / 3906250) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (91 / 5000)) (4051057 / 3906250) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((6435069 / 250000) : ℝ) ≤ Real.exp ((651461 / 200000) - (91 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((651461 / 200000) - (91 / 5000) / 2) (6435069 / 250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (181 / 10000) (91 / 5000) (518431599 / 500000000) (4051057 / 3906250)
    (651461 / 200000) (3258061 / 1000000) (6435069 / 250000) (388496223 / 10000000000) (-220661 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell182 :
    ∀ u : ℝ, u ∈ Set.Icc ((91 / 5000) : ℝ) (183 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1037070591 / 1000000000) : ℝ) ≤ Real.exp (2 * (91 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (91 / 5000)) (1037070591 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((183 / 10000) : ℝ)) ≤ (1037278027 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (183 / 10000)) (1037278027 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25755769 / 1000000) : ℝ) ≤ Real.exp ((3257957 / 1000000) - (183 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3257957 / 1000000) - (183 / 10000) / 2) (25755769 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (91 / 5000) (183 / 10000) (1037070591 / 1000000000) (1037278027 / 1000000000)
    (3257957 / 1000000) (3258713 / 1000000) (25755769 / 1000000) (388262529 / 10000000000) (-441527 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell183 :
    ∀ u : ℝ, u ∈ Set.Icc ((183 / 10000) : ℝ) (23 / 1250) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((518639013 / 500000000) : ℝ) ≤ Real.exp (2 * (183 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (183 / 10000)) (518639013 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((23 / 1250) : ℝ)) ≤ (1037485503 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (23 / 1250)) (1037485503 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25771247 / 1000000) : ℝ) ≤ Real.exp ((203663 / 62500) - (23 / 1250) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((203663 / 62500) - (23 / 1250) / 2) (25771247 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (183 / 10000) (23 / 1250) (518639013 / 500000000) (1037485503 / 1000000000)
    (203663 / 62500) (651873 / 200000) (25771247 / 1000000) (194014671 / 5000000000) (-441733 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell184 :
    ∀ u : ℝ, u ∈ Set.Icc ((23 / 1250) : ℝ) (37 / 2000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((518742751 / 500000000) : ℝ) ≤ Real.exp (2 * (23 / 1250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (23 / 1250)) (518742751 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((37 / 2000) : ℝ)) ≤ (1037693021 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (37 / 2000)) (1037693021 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25786759 / 1000000) : ℝ) ≤ Real.exp ((162963 / 50000) - (37 / 2000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((162963 / 50000) - (37 / 2000) / 2) (25786759 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (23 / 1250) (37 / 2000) (518742751 / 500000000) (1037693021 / 1000000000)
    (162963 / 50000) (3260017 / 1000000) (25786759 / 1000000) (387795923 / 10000000000) (-441939 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell185 :
    ∀ u : ℝ, u ∈ Set.Icc ((37 / 2000) : ℝ) (93 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((51884651 / 50000000) : ℝ) ≤ Real.exp (2 * (37 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (37 / 2000)) (51884651 / 50000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((93 / 5000) : ℝ)) ≤ (1037900581 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (93 / 5000)) (1037900581 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25802281 / 1000000) : ℝ) ≤ Real.exp ((407489 / 125000) - (93 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((407489 / 125000) - (93 / 5000) / 2) (25802281 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (37 / 2000) (93 / 5000) (51884651 / 50000000) (1037900581 / 1000000000)
    (407489 / 125000) (3260669 / 1000000) (25802281 / 1000000) (77512527 / 2000000000) (-55268 / 125) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell186 :
    ∀ u : ℝ, u ∈ Set.Icc ((93 / 5000) : ℝ) (187 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((51895029 / 50000000) : ℝ) ≤ Real.exp (2 * (93 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (93 / 5000)) (51895029 / 50000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((187 / 10000) : ℝ)) ≤ (519054091 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (187 / 10000)) (519054091 / 500000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25817813 / 1000000) : ℝ) ≤ Real.exp ((815141 / 250000) - (187 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((815141 / 250000) - (187 / 10000) / 2) (25817813 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (93 / 5000) (187 / 10000) (51895029 / 50000000) (519054091 / 500000000)
    (815141 / 250000) (3261321 / 1000000) (25817813 / 1000000) (387329477 / 10000000000) (-8847 / 20) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell187 :
    ∀ u : ℝ, u ∈ Set.Icc ((187 / 10000) : ℝ) (47 / 2500) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1038108181 / 1000000000) : ℝ) ≤ Real.exp (2 * (187 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (187 / 10000)) (1038108181 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((47 / 2500) : ℝ)) ≤ (64894739 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (47 / 2500)) (64894739 / 62500000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25833353 / 1000000) : ℝ) ≤ Real.exp ((101913 / 31250) - (47 / 2500) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((101913 / 31250) - (47 / 2500) / 2) (25833353 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (187 / 10000) (47 / 2500) (1038108181 / 1000000000) (64894739 / 62500000)
    (101913 / 31250) (3261973 / 1000000) (25833353 / 1000000) (2419353 / 62500000) (-88511 / 200) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell188 :
    ∀ u : ℝ, u ∈ Set.Icc ((47 / 2500) : ℝ) (189 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1038315823 / 1000000000) : ℝ) ≤ Real.exp (2 * (47 / 2500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (47 / 2500)) (1038315823 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((189 / 10000) : ℝ)) ≤ (259630877 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (189 / 10000)) (259630877 / 250000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25848929 / 1000000) : ℝ) ≤ Real.exp ((3261869 / 1000000) - (189 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3261869 / 1000000) - (189 / 10000) / 2) (25848929 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (47 / 2500) (189 / 10000) (1038315823 / 1000000000) (259630877 / 250000000)
    (3261869 / 1000000) (1631313 / 500000) (25848929 / 1000000) (48357903 / 1250000000) (-442761 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell189 :
    ∀ u : ℝ, u ∈ Set.Icc ((189 / 10000) : ℝ) (19 / 1000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1038523507 / 1000000000) : ℝ) ≤ Real.exp (2 * (189 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (189 / 10000)) (1038523507 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((19 / 1000) : ℝ)) ≤ (1038731233 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (19 / 1000)) (1038731233 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((3233061 / 125000) : ℝ) ≤ Real.exp ((3262521 / 1000000) - (19 / 1000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3262521 / 1000000) - (19 / 1000) / 2) (3233061 / 125000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (189 / 10000) (19 / 1000) (1038523507 / 1000000000) (1038731233 / 1000000000)
    (3262521 / 1000000) (3263279 / 1000000) (3233061 / 125000) (386630503 / 10000000000) (-442967 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cellsBatch018 :
    ∀ u : ℝ, u ∈ Set.Icc ((9 / 500) : ℝ) (19 / 1000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  exact (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell180
      hpThetaCNV_secondDerivative_cell181)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell182
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell183
      hpThetaCNV_secondDerivative_cell184)))
      (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell185
      hpThetaCNV_secondDerivative_cell186)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell187
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell188
      hpThetaCNV_secondDerivative_cell189))))

#print axioms hpThetaCNV_secondDerivative_cellsBatch018
end HodgeProofHP
