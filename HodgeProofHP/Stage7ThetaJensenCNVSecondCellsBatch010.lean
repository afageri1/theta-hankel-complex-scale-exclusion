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

theorem hpThetaCNV_secondDerivative_cell100 :
    ∀ u : ℝ, u ∈ Set.Icc ((1 / 100) : ℝ) (101 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((51010067 / 50000000) : ℝ) ≤ Real.exp (2 * (1 / 100)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1 / 100)) (51010067 / 50000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((101 / 10000) : ℝ)) ≤ (1020405401 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (101 / 10000)) (1020405401 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((24527201 / 1000000) : ℝ) ≤ Real.exp ((1602481 / 500000) - (101 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1602481 / 500000) - (101 / 10000) / 2) (24527201 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (1 / 100) (101 / 10000) (51010067 / 50000000) (1020405401 / 1000000000)
    (1602481 / 500000) (1602853 / 500000) (24527201 / 1000000) (407710607 / 10000000000) (-212281 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell101 :
    ∀ u : ℝ, u ∈ Set.Icc ((101 / 10000) : ℝ) (51 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((5102027 / 5000000) : ℝ) ≤ Real.exp (2 * (101 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (101 / 10000)) (5102027 / 5000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((51 / 5000) : ℝ)) ≤ (1020609503 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (51 / 5000)) (1020609503 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((383464 / 15625) : ℝ) ≤ Real.exp ((3205603 / 1000000) - (51 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3205603 / 1000000) - (51 / 5000) / 2) (383464 / 15625) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (101 / 10000) (51 / 5000) (5102027 / 5000000) (1020609503 / 1000000000)
    (3205603 / 1000000) (3206347 / 1000000) (383464 / 15625) (203734901 / 5000000000) (-424769 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell102 :
    ∀ u : ℝ, u ∈ Set.Icc ((51 / 5000) : ℝ) (103 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((510304751 / 500000000) : ℝ) ≤ Real.exp (2 * (51 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (51 / 5000)) (510304751 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((103 / 10000) : ℝ)) ≤ (204162729 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (103 / 10000)) (204162729 / 200000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((24556199 / 1000000) : ℝ) ≤ Real.exp ((801561 / 250000) - (103 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((801561 / 250000) - (103 / 10000) / 2) (24556199 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (51 / 5000) (103 / 10000) (510304751 / 500000000) (204162729 / 200000000)
    (801561 / 250000) (3206989 / 1000000) (24556199 / 1000000) (407229149 / 10000000000) (-212489 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell103 :
    ∀ u : ℝ, u ∈ Set.Icc ((103 / 10000) : ℝ) (13 / 1250) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((255203411 / 250000000) : ℝ) ≤ Real.exp (2 * (103 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (103 / 10000)) (255203411 / 250000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((13 / 1250) : ℝ)) ≤ (255254457 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (13 / 1250)) (255254457 / 250000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((4914147 / 200000) : ℝ) ≤ Real.exp ((1603443 / 500000) - (13 / 1250) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1603443 / 500000) - (13 / 1250) / 2) (4914147 / 200000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (103 / 10000) (13 / 1250) (255203411 / 250000000) (255254457 / 250000000)
    (1603443 / 500000) (320763 / 100000) (4914147 / 200000) (406988233 / 10000000000) (-85037 / 200) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell104 :
    ∀ u : ℝ, u ∈ Set.Icc ((13 / 1250) : ℝ) (21 / 2000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1021017827 / 1000000000) : ℝ) ≤ Real.exp (2 * (13 / 1250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (13 / 1250)) (1021017827 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((21 / 2000) : ℝ)) ≤ (255305513 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (21 / 2000)) (255305513 / 250000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((4917051 / 200000) : ℝ) ≤ Real.exp ((3207527 / 1000000) - (21 / 2000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3207527 / 1000000) - (21 / 2000) / 2) (4917051 / 200000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (13 / 1250) (21 / 2000) (1021017827 / 1000000000) (255305513 / 250000000)
    (3207527 / 1000000) (200517 / 62500) (4917051 / 200000) (203373933 / 5000000000) (-425393 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell105 :
    ∀ u : ℝ, u ∈ Set.Icc ((21 / 2000) : ℝ) (53 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1021222051 / 1000000000) : ℝ) ≤ Real.exp (2 * (21 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (21 / 2000)) (1021222051 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((53 / 5000) : ℝ)) ≤ (1021426317 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (53 / 5000)) (1021426317 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((24599809 / 1000000) : ℝ) ≤ Real.exp ((3208169 / 1000000) - (53 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3208169 / 1000000) - (53 / 5000) / 2) (24599809 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (21 / 2000) (53 / 5000) (1021222051 / 1000000000) (1021426317 / 1000000000)
    (3208169 / 1000000) (3208913 / 1000000) (24599809 / 1000000) (203253611 / 5000000000) (-425601 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell106 :
    ∀ u : ℝ, u ∈ Set.Icc ((53 / 5000) : ℝ) (107 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((255356579 / 250000000) : ℝ) ≤ Real.exp (2 * (53 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (53 / 5000)) (255356579 / 250000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((107 / 10000) : ℝ)) ≤ (1021630623 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (107 / 10000)) (1021630623 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((12307173 / 500000) : ℝ) ≤ Real.exp ((320881 / 100000) - (107 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((320881 / 100000) - (107 / 10000) / 2) (12307173 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (53 / 5000) (107 / 10000) (255356579 / 250000000) (1021630623 / 1000000000)
    (320881 / 100000) (641911 / 200000) (12307173 / 500000) (203133571 / 5000000000) (-425809 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell107 :
    ∀ u : ℝ, u ∈ Set.Icc ((107 / 10000) : ℝ) (27 / 2500) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((510815311 / 500000000) : ℝ) ≤ Real.exp (2 * (107 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (107 / 10000)) (510815311 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((27 / 2500) : ℝ)) ≤ (1021834969 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (27 / 2500)) (1021834969 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((24628917 / 1000000) : ℝ) ≤ Real.exp ((802363 / 250000) - (27 / 2500) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((802363 / 250000) - (27 / 2500) / 2) (24628917 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (107 / 10000) (27 / 2500) (510815311 / 500000000) (1021834969 / 1000000000)
    (802363 / 250000) (3210197 / 1000000) (24628917 / 1000000) (203013393 / 5000000000) (-53252 / 125) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell108 :
    ∀ u : ℝ, u ∈ Set.Icc ((27 / 2500) : ℝ) (109 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((127729371 / 125000000) : ℝ) ≤ Real.exp (2 * (27 / 2500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (27 / 2500)) (127729371 / 125000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((109 / 10000) : ℝ)) ≤ (1022039357 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (109 / 10000)) (1022039357 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((3080437 / 125000) : ℝ) ≤ Real.exp ((1605047 / 500000) - (109 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1605047 / 500000) - (109 / 10000) / 2) (3080437 / 125000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (27 / 2500) (109 / 10000) (127729371 / 125000000) (1022039357 / 1000000000)
    (1605047 / 500000) (3210839 / 1000000) (3080437 / 125000) (202893291 / 5000000000) (-53278 / 125) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell109 :
    ∀ u : ℝ, u ∈ Set.Icc ((109 / 10000) : ℝ) (11 / 1000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((255509839 / 250000000) : ℝ) ≤ Real.exp (2 * (109 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (109 / 10000)) (255509839 / 250000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((11 / 1000) : ℝ)) ≤ (204448757 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (11 / 1000)) (204448757 / 200000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((6164521 / 250000) : ℝ) ≤ Real.exp ((200671 / 62500) - (11 / 1000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((200671 / 62500) - (11 / 1000) / 2) (6164521 / 250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (109 / 10000) (11 / 1000) (255509839 / 250000000) (204448757 / 200000000)
    (200671 / 62500) (1605741 / 500000) (6164521 / 250000) (202773257 / 5000000000) (-53304 / 125) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cellsBatch010 :
    ∀ u : ℝ, u ∈ Set.Icc ((1 / 100) : ℝ) (11 / 1000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  exact (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell100
      hpThetaCNV_secondDerivative_cell101)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell102
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell103
      hpThetaCNV_secondDerivative_cell104)))
      (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell105
      hpThetaCNV_secondDerivative_cell106)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell107
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell108
      hpThetaCNV_secondDerivative_cell109))))

#print axioms hpThetaCNV_secondDerivative_cellsBatch010
end HodgeProofHP
