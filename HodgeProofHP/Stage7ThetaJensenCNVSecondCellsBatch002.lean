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

theorem hpThetaCNV_secondDerivative_cell020 :
    ∀ u : ℝ, u ∈ Set.Icc ((1 / 500) : ℝ) (21 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((100400801 / 100000000) : ℝ) ≤ Real.exp (2 * (1 / 500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1 / 500)) (100400801 / 100000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((21 / 10000) : ℝ)) ≤ (1004208833 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (21 / 10000)) (1004208833 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((11702247 / 500000) : ℝ) ≤ Real.exp ((3154091 / 1000000) - (21 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3154091 / 1000000) - (21 / 10000) / 2) (11702247 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (1 / 500) (21 / 10000) (100400801 / 100000000) (1004208833 / 1000000000)
    (3154091 / 1000000) (3154823 / 1000000) (11702247 / 500000) (42726837 / 1000000000) (-203941 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell021 :
    ∀ u : ℝ, u ∈ Set.Icc ((21 / 10000) : ℝ) (11 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((15690763 / 15625000) : ℝ) ≤ Real.exp (2 * (21 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (21 / 10000)) (15690763 / 15625000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((11 / 5000) : ℝ)) ≤ (200881939 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (11 / 5000)) (200881939 / 200000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((23418091 / 1000000) : ℝ) ≤ Real.exp ((1577361 / 500000) - (11 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1577361 / 500000) - (11 / 5000) / 2) (23418091 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (21 / 10000) (11 / 5000) (15690763 / 15625000) (200881939 / 200000000)
    (1577361 / 500000) (1577727 / 500000) (23418091 / 1000000) (42702029 / 1000000000) (-408091 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell022 :
    ∀ u : ℝ, u ∈ Set.Icc ((11 / 5000) : ℝ) (23 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((502204847 / 500000000) : ℝ) ≤ Real.exp (2 * (11 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (11 / 5000)) (502204847 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((23 / 10000) : ℝ)) ≤ (1004610597 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (23 / 10000)) (1004610597 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((23431697 / 1000000) : ℝ) ≤ Real.exp ((3155353 / 1000000) - (23 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3155353 / 1000000) - (23 / 10000) / 2) (23431697 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (11 / 5000) (23 / 10000) (502204847 / 500000000) (1004610597 / 1000000000)
    (3155353 / 1000000) (631217 / 200000) (23431697 / 1000000) (213386167 / 5000000000) (-4083 / 10) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell023 :
    ∀ u : ℝ, u ∈ Set.Icc ((23 / 10000) : ℝ) (3 / 1250) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((251152649 / 250000000) : ℝ) ≤ Real.exp (2 * (23 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (23 / 10000)) (251152649 / 250000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((3 / 1250) : ℝ)) ≤ (1004811539 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3 / 1250)) (1004811539 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((2344531 / 100000) : ℝ) ≤ Real.exp ((197249 / 62500) - (3 / 1250) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((197249 / 62500) - (3 / 1250) / 2) (2344531 / 100000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (23 / 10000) (3 / 1250) (251152649 / 250000000) (1004811539 / 1000000000)
    (197249 / 62500) (789179 / 250000) (2344531 / 100000) (213262269 / 5000000000) (-408509 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell024 :
    ∀ u : ℝ, u ∈ Set.Icc ((3 / 1250) : ℝ) (1 / 400) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((502405769 / 500000000) : ℝ) ≤ Real.exp (2 * (3 / 1250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3 / 1250)) (502405769 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((1 / 400) : ℝ)) ≤ (1005012521 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1 / 400)) (1005012521 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((23458931 / 1000000) : ℝ) ≤ Real.exp ((631323 / 200000) - (1 / 400) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((631323 / 200000) - (1 / 400) / 2) (23458931 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (3 / 1250) (1 / 400) (502405769 / 500000000) (1005012521 / 1000000000)
    (631323 / 200000) (789337 / 250000) (23458931 / 1000000) (106569221 / 2500000000) (-204359 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell025 :
    ∀ u : ℝ, u ∈ Set.Icc ((1 / 400) : ℝ) (13 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((25125313 / 25000000) : ℝ) ≤ Real.exp (2 * (1 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1 / 400)) (25125313 / 25000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((13 / 5000) : ℝ)) ≤ (125651693 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (13 / 5000)) (125651693 / 125000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((293407 / 12500) : ℝ) ≤ Real.exp ((1578623 / 500000) - (13 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1578623 / 500000) - (13 / 5000) / 2) (293407 / 12500) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (1 / 400) (13 / 5000) (25125313 / 25000000) (125651693 / 125000000)
    (1578623 / 500000) (3157979 / 1000000) (293407 / 12500) (426029373 / 10000000000) (-408927 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell026 :
    ∀ u : ℝ, u ∈ Set.Icc ((13 / 5000) : ℝ) (27 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1005213543 / 1000000000) : ℝ) ≤ Real.exp (2 * (13 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (13 / 5000)) (1005213543 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((27 / 10000) : ℝ)) ≤ (1005414607 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (27 / 10000)) (1005414607 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((23486221 / 1000000) : ℝ) ≤ Real.exp ((1578939 / 500000) - (27 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1578939 / 500000) - (27 / 10000) / 2) (23486221 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (13 / 5000) (27 / 10000) (1005213543 / 1000000000) (1005414607 / 1000000000)
    (1578939 / 500000) (3158611 / 1000000) (23486221 / 1000000) (6652837 / 156250000) (-51142 / 125) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell027 :
    ∀ u : ℝ, u ∈ Set.Icc ((27 / 10000) : ℝ) (7 / 2500) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((502707303 / 500000000) : ℝ) ≤ Real.exp (2 * (27 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (27 / 10000)) (502707303 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((7 / 2500) : ℝ)) ≤ (100561571 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (7 / 2500)) (100561571 / 100000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((11749933 / 500000) : ℝ) ≤ Real.exp ((3158509 / 1000000) - (7 / 2500) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3158509 / 1000000) - (7 / 2500) / 2) (11749933 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (27 / 10000) (7 / 2500) (502707303 / 500000000) (100561571 / 100000000)
    (3158509 / 1000000) (3159243 / 1000000) (11749933 / 500000) (212767171 / 5000000000) (-81869 / 200) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell028 :
    ∀ u : ℝ, u ∈ Set.Icc ((7 / 2500) : ℝ) (29 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1005615709 / 1000000000) : ℝ) ≤ Real.exp (2 * (7 / 2500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (7 / 2500)) (1005615709 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((29 / 10000) : ℝ)) ≤ (1005816853 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (29 / 10000)) (1005816853 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((11756771 / 500000) : ℝ) ≤ Real.exp ((3159141 / 1000000) - (29 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3159141 / 1000000) - (29 / 10000) / 2) (11756771 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (7 / 2500) (29 / 10000) (1005615709 / 1000000000) (1005816853 / 1000000000)
    (3159141 / 1000000) (25279 / 8000) (11756771 / 500000) (212643421 / 5000000000) (-409553 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell029 :
    ∀ u : ℝ, u ∈ Set.Icc ((29 / 10000) : ℝ) (3 / 1000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((251454213 / 250000000) : ℝ) ≤ Real.exp (2 * (29 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (29 / 10000)) (251454213 / 250000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((3 / 1000) : ℝ)) ≤ (1006018037 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3 / 1000)) (1006018037 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((11763613 / 500000) : ℝ) ≤ Real.exp ((3159773 / 1000000) - (3 / 1000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3159773 / 1000000) - (3 / 1000) / 2) (11763613 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (29 / 10000) (3 / 1000) (251454213 / 250000000) (1006018037 / 1000000000)
    (3159773 / 1000000) (3160507 / 1000000) (11763613 / 500000) (85007897 / 2000000000) (-204881 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cellsBatch002 :
    ∀ u : ℝ, u ∈ Set.Icc ((1 / 500) : ℝ) (3 / 1000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  exact (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell020
      hpThetaCNV_secondDerivative_cell021)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell022
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell023
      hpThetaCNV_secondDerivative_cell024)))
      (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell025
      hpThetaCNV_secondDerivative_cell026)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell027
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell028
      hpThetaCNV_secondDerivative_cell029))))

#print axioms hpThetaCNV_secondDerivative_cellsBatch002
end HodgeProofHP
