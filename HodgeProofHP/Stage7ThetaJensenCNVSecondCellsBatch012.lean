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

theorem hpThetaCNV_secondDerivative_cell120 :
    ∀ u : ℝ, u ∈ Set.Icc ((3 / 250) : ℝ) (121 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1024290317 / 1000000000) : ℝ) ≤ Real.exp (2 * (3 / 250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3 / 250)) (1024290317 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((121 / 10000) : ℝ)) ≤ (1024495197 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (121 / 10000)) (1024495197 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((3102421 / 125000) : ℝ) ≤ Real.exp ((201113 / 62500) - (121 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((201113 / 62500) - (121 / 10000) / 2) (3102421 / 125000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (3 / 250) (121 / 10000) (1024290317 / 1000000000) (1024495197 / 1000000000)
    (201113 / 62500) (643711 / 200000) (3102421 / 125000) (201455573 / 5000000000) (-107179 / 250) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell121 :
    ∀ u : ℝ, u ∈ Set.Icc ((121 / 10000) : ℝ) (61 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((256123799 / 250000000) : ℝ) ≤ Real.exp (2 * (121 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (121 / 10000)) (256123799 / 250000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((61 / 5000) : ℝ)) ≤ (256175029 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (61 / 5000)) (256175029 / 250000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((4966817 / 200000) : ℝ) ≤ Real.exp ((3218451 / 1000000) - (61 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3218451 / 1000000) - (61 / 5000) / 2) (4966817 / 200000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (121 / 10000) (61 / 5000) (256123799 / 250000000) (256175029 / 250000000)
    (3218451 / 1000000) (1609599 / 500000) (4966817 / 200000) (50334047 / 1250000000) (-428923 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell122 :
    ∀ u : ℝ, u ∈ Set.Icc ((61 / 5000) : ℝ) (123 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((204940023 / 200000000) : ℝ) ≤ Real.exp (2 * (61 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (61 / 5000)) (204940023 / 200000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((123 / 10000) : ℝ)) ≤ (1024905077 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (123 / 10000)) (1024905077 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((4969767 / 200000) : ℝ) ≤ Real.exp ((643819 / 200000) - (123 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((643819 / 200000) - (123 / 10000) / 2) (4969767 / 200000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (61 / 5000) (123 / 10000) (204940023 / 200000000) (1024905077 / 1000000000)
    (643819 / 200000) (1609921 / 500000) (4969767 / 200000) (201216677 / 5000000000) (-42913 / 100) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell123 :
    ∀ u : ℝ, u ∈ Set.Icc ((123 / 10000) : ℝ) (31 / 2500) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((256226269 / 250000000) : ℝ) ≤ Real.exp (2 * (123 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (123 / 10000)) (256226269 / 250000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((31 / 2500) : ℝ)) ≤ (1025110079 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (31 / 2500)) (1025110079 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((12431797 / 500000) : ℝ) ≤ Real.exp ((3219739 / 1000000) - (31 / 2500) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3219739 / 1000000) - (31 / 2500) / 2) (12431797 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (123 / 10000) (31 / 2500) (256226269 / 250000000) (1025110079 / 1000000000)
    (3219739 / 1000000) (1610243 / 500000) (12431797 / 500000) (40219447 / 1000000000) (-214669 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell124 :
    ∀ u : ℝ, u ∈ Set.Icc ((31 / 2500) : ℝ) (1 / 80) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((512555039 / 500000000) : ℝ) ≤ Real.exp (2 * (31 / 2500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (31 / 2500)) (512555039 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((1 / 80) : ℝ)) ≤ (1025315121 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1 / 80)) (1025315121 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((12439181 / 500000) : ℝ) ≤ Real.exp ((3220383 / 1000000) - (1 / 80) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3220383 / 1000000) - (1 / 80) / 2) (12439181 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (31 / 2500) (1 / 80) (512555039 / 500000000) (1025315121 / 1000000000)
    (3220383 / 1000000) (322113 / 100000) (12439181 / 500000) (100488931 / 2500000000) (-85909 / 200) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell125 :
    ∀ u : ℝ, u ∈ Set.Icc ((1 / 80) : ℝ) (63 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((12816439 / 12500000) : ℝ) ≤ Real.exp (2 * (1 / 80)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1 / 80)) (12816439 / 12500000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((63 / 5000) : ℝ)) ≤ (205104041 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (63 / 5000)) (205104041 / 200000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((24893139 / 1000000) : ℝ) ≤ Real.exp ((3221027 / 1000000) - (63 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3221027 / 1000000) - (63 / 5000) / 2) (24893139 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (1 / 80) (63 / 5000) (12816439 / 12500000) (205104041 / 200000000)
    (3221027 / 1000000) (128871 / 40000) (24893139 / 1000000) (100429279 / 2500000000) (-429753 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell126 :
    ∀ u : ℝ, u ∈ Set.Icc ((63 / 5000) : ℝ) (127 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((256380051 / 250000000) : ℝ) ≤ Real.exp (2 * (63 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (63 / 5000)) (256380051 / 250000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((127 / 10000) : ℝ)) ≤ (1025725329 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (127 / 10000)) (1025725329 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((6226981 / 250000) : ℝ) ≤ Real.exp ((3221671 / 1000000) - (127 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3221671 / 1000000) - (127 / 10000) / 2) (6226981 / 250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (63 / 5000) (127 / 10000) (256380051 / 250000000) (1025725329 / 1000000000)
    (3221671 / 1000000) (3222419 / 1000000) (6226981 / 250000) (200739331 / 5000000000) (-10749 / 25) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell127 :
    ∀ u : ℝ, u ∈ Set.Icc ((127 / 10000) : ℝ) (8 / 625) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((64107833 / 62500000) : ℝ) ≤ Real.exp (2 * (127 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (127 / 10000)) (64107833 / 62500000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((8 / 625) : ℝ)) ≤ (205186099 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (8 / 625)) (205186099 / 200000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((24922743 / 1000000) : ℝ) ≤ Real.exp ((805579 / 250000) - (8 / 625) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((805579 / 250000) - (8 / 625) / 2) (24922743 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (127 / 10000) (8 / 625) (64107833 / 62500000) (205186099 / 200000000)
    (805579 / 250000) (402883 / 125000) (24922743 / 1000000) (50154993 / 1250000000) (-430167 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell128 :
    ∀ u : ℝ, u ∈ Set.Icc ((8 / 625) : ℝ) (129 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((512965247 / 500000000) : ℝ) ≤ Real.exp (2 * (8 / 625)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (8 / 625)) (512965247 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((129 / 10000) : ℝ)) ≤ (1026135701 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (129 / 10000)) (1026135701 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((12468773 / 500000) : ℝ) ≤ Real.exp ((40287 / 12500) - (129 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((40287 / 12500) - (129 / 10000) / 2) (12468773 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (8 / 625) (129 / 10000) (512965247 / 500000000) (1026135701 / 1000000000)
    (40287 / 12500) (805927 / 250000) (12468773 / 500000) (401001767 / 10000000000) (-215187 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell129 :
    ∀ u : ℝ, u ∈ Set.Icc ((129 / 10000) : ℝ) (13 / 1000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((10261357 / 10000000) : ℝ) ≤ Real.exp (2 * (129 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (129 / 10000)) (10261357 / 10000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((13 / 1000) : ℝ)) ≤ (1026340949 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (13 / 1000)) (1026340949 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((12476191 / 500000) : ℝ) ≤ Real.exp ((644721 / 200000) - (13 / 1000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((644721 / 200000) - (13 / 1000) / 2) (12476191 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (129 / 10000) (13 / 1000) (10261357 / 10000000) (1026340949 / 1000000000)
    (644721 / 200000) (3224353 / 1000000) (12476191 / 500000) (200381671 / 5000000000) (-215291 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cellsBatch012 :
    ∀ u : ℝ, u ∈ Set.Icc ((3 / 250) : ℝ) (13 / 1000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  exact (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell120
      hpThetaCNV_secondDerivative_cell121)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell122
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell123
      hpThetaCNV_secondDerivative_cell124)))
      (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell125
      hpThetaCNV_secondDerivative_cell126)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell127
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell128
      hpThetaCNV_secondDerivative_cell129))))

#print axioms hpThetaCNV_secondDerivative_cellsBatch012
end HodgeProofHP
