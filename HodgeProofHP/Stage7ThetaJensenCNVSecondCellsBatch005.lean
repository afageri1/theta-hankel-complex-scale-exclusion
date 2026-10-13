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

theorem hpThetaCNV_secondDerivative_cell050 :
    ∀ u : ℝ, u ∈ Set.Icc ((1 / 200) : ℝ) (51 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1010050167 / 1000000000) : ℝ) ≤ Real.exp (2 * (1 / 200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1 / 200)) (1010050167 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((51 / 10000) : ℝ)) ≤ (505126099 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (51 / 10000)) (505126099 / 500000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((4763417 / 200000) : ℝ) ≤ Real.exp ((198317 / 62500) - (51 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((198317 / 62500) - (51 / 10000) / 2) (4763417 / 200000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (1 / 200) (51 / 10000) (1010050167 / 1000000000) (505126099 / 500000000)
    (198317 / 62500) (3173809 / 1000000) (4763417 / 200000) (419866663 / 10000000000) (-207073 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell051 :
    ∀ u : ℝ, u ∈ Set.Icc ((51 / 10000) : ℝ) (13 / 2500) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1010252197 / 1000000000) : ℝ) ≤ Real.exp (2 * (51 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (51 / 10000)) (1010252197 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((13 / 2500) : ℝ)) ≤ (252613567 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (13 / 2500)) (252613567 / 250000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((23831017 / 1000000) : ℝ) ≤ Real.exp ((3173707 / 1000000) - (13 / 2500) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3173707 / 1000000) - (13 / 2500) / 2) (23831017 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (51 / 10000) (13 / 2500) (1010252197 / 1000000000) (252613567 / 250000000)
    (3173707 / 1000000) (793611 / 250000) (23831017 / 1000000) (419621203 / 10000000000) (-82871 / 200) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell052 :
    ∀ u : ℝ, u ∈ Set.Icc ((13 / 2500) : ℝ) (53 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1010454267 / 1000000000) : ℝ) ≤ Real.exp (2 * (13 / 2500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (13 / 2500)) (1010454267 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((53 / 10000) : ℝ)) ≤ (50532819 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (53 / 10000)) (50532819 / 50000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((11922479 / 500000) : ℝ) ≤ Real.exp ((1587171 / 500000) - (53 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1587171 / 500000) - (53 / 10000) / 2) (11922479 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (13 / 2500) (53 / 10000) (1010454267 / 1000000000) (50532819 / 50000000)
    (1587171 / 500000) (3175079 / 1000000) (11922479 / 500000) (41937587 / 1000000000) (-414563 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell053 :
    ∀ u : ℝ, u ∈ Set.Icc ((53 / 10000) : ℝ) (27 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1010656379 / 1000000000) : ℝ) ≤ Real.exp (2 * (53 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (53 / 10000)) (1010656379 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((27 / 5000) : ℝ)) ≤ (1010858531 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (27 / 5000)) (1010858531 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((11929453 / 500000) : ℝ) ≤ Real.exp ((3174977 / 1000000) - (27 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3174977 / 1000000) - (27 / 5000) / 2) (11929453 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (53 / 10000) (27 / 5000) (1010656379 / 1000000000) (1010858531 / 1000000000)
    (3174977 / 1000000) (1587857 / 500000) (11929453 / 500000) (209565351 / 5000000000) (-103693 / 250) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell054 :
    ∀ u : ℝ, u ∈ Set.Icc ((27 / 5000) : ℝ) (11 / 2000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((101085853 / 100000000) : ℝ) ≤ Real.exp (2 * (27 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (27 / 5000)) (101085853 / 100000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((11 / 2000) : ℝ)) ≤ (1011060723 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (11 / 2000)) (1011060723 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((23872863 / 1000000) : ℝ) ≤ Real.exp ((793903 / 250000) - (11 / 2000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((793903 / 250000) - (11 / 2000) / 2) (23872863 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (27 / 5000) (11 / 2000) (101085853 / 100000000) (1011060723 / 1000000000)
    (793903 / 250000) (3176349 / 1000000) (23872863 / 1000000) (209442831 / 5000000000) (-414981 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell055 :
    ∀ u : ℝ, u ∈ Set.Icc ((11 / 2000) : ℝ) (7 / 1250) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((505530361 / 500000000) : ℝ) ≤ Real.exp (2 * (11 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (11 / 2000)) (505530361 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((7 / 1250) : ℝ)) ≤ (202252591 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (7 / 1250)) (202252591 / 200000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((5971707 / 250000) : ℝ) ≤ Real.exp ((3176247 / 1000000) - (7 / 1250) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3176247 / 1000000) - (7 / 1250) / 2) (5971707 / 250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (11 / 2000) (7 / 1250) (505530361 / 500000000) (202252591 / 200000000)
    (3176247 / 1000000) (397123 / 125000) (5971707 / 250000) (3270631 / 78125000) (-415189 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell056 :
    ∀ u : ℝ, u ∈ Set.Icc ((7 / 1250) : ℝ) (57 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((505631477 / 500000000) : ℝ) ≤ Real.exp (2 * (7 / 1250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (7 / 1250)) (505631477 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((57 / 10000) : ℝ)) ≤ (252866307 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (57 / 10000)) (252866307 / 250000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((23900801 / 1000000) : ℝ) ≤ Real.exp ((1588441 / 500000) - (57 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1588441 / 500000) - (57 / 10000) / 2) (23900801 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (7 / 1250) (57 / 10000) (505631477 / 500000000) (252866307 / 250000000)
    (1588441 / 500000) (158881 / 50000) (23900801 / 1000000) (20919801 / 500000000) (-207699 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell057 :
    ∀ u : ℝ, u ∈ Set.Icc ((57 / 10000) : ℝ) (29 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1011465227 / 1000000000) : ℝ) ≤ Real.exp (2 * (57 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (57 / 10000)) (1011465227 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((29 / 5000) : ℝ)) ≤ (1011667541 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (29 / 5000)) (1011667541 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((11957403 / 500000) : ℝ) ≤ Real.exp ((1588759 / 500000) - (29 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1588759 / 500000) - (29 / 5000) / 2) (11957403 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (57 / 10000) (29 / 5000) (1011465227 / 1000000000) (1011667541 / 1000000000)
    (1588759 / 500000) (635651 / 200000) (11957403 / 500000) (418150999 / 10000000000) (-207803 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell058 :
    ∀ u : ℝ, u ∈ Set.Icc ((29 / 5000) : ℝ) (59 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((50583377 / 50000000) : ℝ) ≤ Real.exp (2 * (29 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (29 / 5000)) (50583377 / 50000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((59 / 10000) : ℝ)) ≤ (202373979 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (59 / 10000)) (202373979 / 200000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((5982199 / 250000) : ℝ) ≤ Real.exp ((3178153 / 1000000) - (59 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3178153 / 1000000) - (59 / 10000) / 2) (5982199 / 250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (29 / 5000) (59 / 10000) (50583377 / 50000000) (202373979 / 200000000)
    (3178153 / 1000000) (3178891 / 1000000) (5982199 / 250000) (208953263 / 5000000000) (-83163 / 200) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell059 :
    ∀ u : ℝ, u ∈ Set.Icc ((59 / 10000) : ℝ) (3 / 500) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((505934947 / 500000000) : ℝ) ≤ Real.exp (2 * (59 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (59 / 10000)) (505934947 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((3 / 500) : ℝ)) ≤ (1012072289 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3 / 500)) (1012072289 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((23942817 / 1000000) : ℝ) ≤ Real.exp ((3178789 / 1000000) - (3 / 500) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3178789 / 1000000) - (3 / 500) / 2) (23942817 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (59 / 10000) (3 / 500) (505934947 / 500000000) (1012072289 / 1000000000)
    (3178789 / 1000000) (3179527 / 1000000) (23942817 / 1000000) (417661799 / 10000000000) (-52003 / 125) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cellsBatch005 :
    ∀ u : ℝ, u ∈ Set.Icc ((1 / 200) : ℝ) (3 / 500) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  exact (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell050
      hpThetaCNV_secondDerivative_cell051)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell052
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell053
      hpThetaCNV_secondDerivative_cell054)))
      (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell055
      hpThetaCNV_secondDerivative_cell056)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell057
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell058
      hpThetaCNV_secondDerivative_cell059))))

#print axioms hpThetaCNV_secondDerivative_cellsBatch005
end HodgeProofHP
