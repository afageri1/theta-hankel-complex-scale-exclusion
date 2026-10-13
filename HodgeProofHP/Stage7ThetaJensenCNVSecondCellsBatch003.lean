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

theorem hpThetaCNV_secondDerivative_cell030 :
    ∀ u : ℝ, u ∈ Set.Icc ((3 / 1000) : ℝ) (31 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((251504509 / 250000000) : ℝ) ≤ Real.exp (2 * (3 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3 / 1000)) (251504509 / 250000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((31 / 10000) : ℝ)) ≤ (50310963 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (31 / 10000)) (50310963 / 50000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((23540919 / 1000000) : ℝ) ≤ Real.exp ((632081 / 200000) - (31 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((632081 / 200000) - (31 / 10000) / 2) (23540919 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (3 / 1000) (31 / 10000) (251504509 / 250000000) (50310963 / 50000000)
    (632081 / 200000) (3161139 / 1000000) (23540919 / 1000000) (424792253 / 10000000000) (-409971 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell031 :
    ∀ u : ℝ, u ∈ Set.Icc ((31 / 10000) : ℝ) (2 / 625) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1006219259 / 1000000000) : ℝ) ≤ Real.exp (2 * (31 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (31 / 10000)) (1006219259 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((2 / 625) : ℝ)) ≤ (251605131 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2 / 625)) (251605131 / 250000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((23554619 / 1000000) : ℝ) ≤ Real.exp ((3161037 / 1000000) - (2 / 625) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3161037 / 1000000) - (2 / 625) / 2) (23554619 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (31 / 10000) (2 / 625) (1006219259 / 1000000000) (251605131 / 250000000)
    (3161037 / 1000000) (3161771 / 1000000) (23554619 / 1000000) (212272591 / 5000000000) (-20509 / 50) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell032 :
    ∀ u : ℝ, u ∈ Set.Icc ((2 / 625) : ℝ) (33 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1006420523 / 1000000000) : ℝ) ≤ Real.exp (2 * (2 / 625)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2 / 625)) (1006420523 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((33 / 10000) : ℝ)) ≤ (251655457 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (33 / 10000)) (251655457 / 250000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((23568351 / 1000000) : ℝ) ≤ Real.exp ((316167 / 100000) - (33 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((316167 / 100000) - (33 / 10000) / 2) (23568351 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (2 / 625) (33 / 10000) (1006420523 / 1000000000) (251655457 / 250000000)
    (316167 / 100000) (790601 / 250000) (23568351 / 1000000) (424297823 / 10000000000) (-410389 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell033 :
    ∀ u : ℝ, u ∈ Set.Icc ((33 / 10000) : ℝ) (17 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1006621827 / 1000000000) : ℝ) ≤ Real.exp (2 * (33 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (33 / 10000)) (1006621827 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((17 / 5000) : ℝ)) ≤ (1006823173 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (17 / 5000)) (1006823173 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((23582067 / 1000000) : ℝ) ≤ Real.exp ((1581151 / 500000) - (17 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1581151 / 500000) - (17 / 5000) / 2) (23582067 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (33 / 10000) (17 / 5000) (1006621827 / 1000000000) (1006823173 / 1000000000)
    (1581151 / 500000) (790759 / 250000) (23582067 / 1000000) (424051039 / 10000000000) (-410597 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell034 :
    ∀ u : ℝ, u ∈ Set.Icc ((17 / 5000) : ℝ) (7 / 2000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((251705793 / 250000000) : ℝ) ≤ Real.exp (2 * (17 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (17 / 5000)) (251705793 / 250000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((7 / 2000) : ℝ)) ≤ (503512279 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (7 / 2000)) (503512279 / 500000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((23595791 / 1000000) : ℝ) ≤ Real.exp ((1581467 / 500000) - (7 / 2000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1581467 / 500000) - (7 / 2000) / 2) (23595791 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (17 / 5000) (7 / 2000) (251705793 / 250000000) (503512279 / 500000000)
    (1581467 / 500000) (3163669 / 1000000) (23595791 / 1000000) (211902199 / 5000000000) (-205403 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell035 :
    ∀ u : ℝ, u ∈ Set.Icc ((7 / 2000) : ℝ) (9 / 2500) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1007024557 / 1000000000) : ℝ) ≤ Real.exp (2 * (7 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (7 / 2000)) (1007024557 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((9 / 2500) : ℝ)) ≤ (1007225983 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9 / 2500)) (1007225983 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((23609547 / 1000000) : ℝ) ≤ Real.exp ((3163567 / 1000000) - (9 / 2500) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3163567 / 1000000) - (9 / 2500) / 2) (23609547 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (7 / 2000) (9 / 2500) (1007024557 / 1000000000) (1007225983 / 1000000000)
    (3163567 / 1000000) (1582151 / 500000) (23609547 / 1000000) (423557471 / 10000000000) (-82203 / 200) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell036 :
    ∀ u : ℝ, u ∈ Set.Icc ((9 / 2500) : ℝ) (37 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((503612991 / 500000000) : ℝ) ≤ Real.exp (2 * (9 / 2500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9 / 2500)) (503612991 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((37 / 10000) : ℝ)) ≤ (125928431 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (37 / 10000)) (125928431 / 125000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((2362331 / 100000) : ℝ) ≤ Real.exp ((15821 / 5000) - (37 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((15821 / 5000) - (37 / 10000) / 2) (2362331 / 100000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (9 / 2500) (37 / 10000) (503612991 / 500000000) (125928431 / 125000000)
    (15821 / 5000) (632987 / 200000) (2362331 / 100000) (84662141 / 2000000000) (-51403 / 125) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell037 :
    ∀ u : ℝ, u ∈ Set.Icc ((37 / 10000) : ℝ) (19 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1007427447 / 1000000000) : ℝ) ≤ Real.exp (2 * (37 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (37 / 10000)) (1007427447 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((19 / 5000) : ℝ)) ≤ (503814477 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (19 / 5000)) (503814477 / 500000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((11818541 / 500000) : ℝ) ≤ Real.exp ((3164833 / 1000000) - (19 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3164833 / 1000000) - (19 / 5000) / 2) (11818541 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (37 / 10000) (19 / 5000) (1007427447 / 1000000000) (503814477 / 500000000)
    (3164833 / 1000000) (49462 / 15625) (11818541 / 500000) (211532033 / 5000000000) (-411433 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell038 :
    ∀ u : ℝ, u ∈ Set.Icc ((19 / 5000) : ℝ) (39 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1007628953 / 1000000000) : ℝ) ≤ Real.exp (2 * (19 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (19 / 5000)) (1007628953 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((39 / 10000) : ℝ)) ≤ (2015661 / 2000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (39 / 10000)) (2015661 / 2000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((11825431 / 500000) : ℝ) ≤ Real.exp ((1582733 / 500000) - (39 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1582733 / 500000) - (39 / 10000) / 2) (11825431 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (19 / 5000) (39 / 10000) (1007628953 / 1000000000) (2015661 / 2000000)
    (1582733 / 500000) (3166201 / 1000000) (11825431 / 500000) (422817571 / 10000000000) (-205821 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell039 :
    ∀ u : ℝ, u ∈ Set.Icc ((39 / 10000) : ℝ) (1 / 250) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1007830499 / 1000000000) : ℝ) ≤ Real.exp (2 * (39 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (39 / 10000)) (1007830499 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((1 / 250) : ℝ)) ≤ (504016043 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1 / 250)) (504016043 / 500000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((473293 / 20000) : ℝ) ≤ Real.exp ((3166099 / 1000000) - (1 / 250) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3166099 / 1000000) - (1 / 250) / 2) (473293 / 20000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (39 / 10000) (1 / 250) (1007830499 / 1000000000) (504016043 / 500000000)
    (3166099 / 1000000) (1583417 / 500000) (473293 / 20000) (21128561 / 500000000) (-8237 / 20) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cellsBatch003 :
    ∀ u : ℝ, u ∈ Set.Icc ((3 / 1000) : ℝ) (1 / 250) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  exact (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell030
      hpThetaCNV_secondDerivative_cell031)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell032
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell033
      hpThetaCNV_secondDerivative_cell034)))
      (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell035
      hpThetaCNV_secondDerivative_cell036)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell037
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell038
      hpThetaCNV_secondDerivative_cell039))))

#print axioms hpThetaCNV_secondDerivative_cellsBatch003
end HodgeProofHP
