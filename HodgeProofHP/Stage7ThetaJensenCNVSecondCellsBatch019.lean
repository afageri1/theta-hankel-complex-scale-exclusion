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

theorem hpThetaCNV_secondDerivative_cell190 :
    ∀ u : ℝ, u ∈ Set.Icc ((19 / 1000) : ℝ) (191 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((32460351 / 31250000) : ℝ) ≤ Real.exp (2 * (19 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (19 / 1000)) (32460351 / 31250000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((191 / 10000) : ℝ)) ≤ (1038939 / 1000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (191 / 10000)) (1038939 / 1000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((12940041 / 500000) : ℝ) ≤ Real.exp ((1631587 / 500000) - (191 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1631587 / 500000) - (191 / 10000) / 2) (12940041 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (19 / 1000) (191 / 10000) (32460351 / 31250000) (1038939 / 1000000)
    (1631587 / 500000) (3263931 / 1000000) (12940041 / 500000) (19319877 / 500000000) (-110793 / 250) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell191 :
    ∀ u : ℝ, u ∈ Set.Icc ((191 / 10000) : ℝ) (12 / 625) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1038938999 / 1000000000) : ℝ) ≤ Real.exp (2 * (191 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (191 / 10000)) (1038938999 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((12 / 625) : ℝ)) ≤ (1039146809 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (12 / 625)) (1039146809 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((1294783 / 50000) : ℝ) ≤ Real.exp ((1631913 / 500000) - (12 / 625) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1631913 / 500000) - (12 / 625) / 2) (1294783 / 50000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (191 / 10000) (12 / 625) (1038938999 / 1000000000) (1039146809 / 1000000000)
    (1631913 / 500000) (408073 / 125000) (1294783 / 50000) (77233019 / 2000000000) (-443377 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell192 :
    ∀ u : ℝ, u ∈ Set.Icc ((12 / 625) : ℝ) (193 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((129893351 / 125000000) : ℝ) ≤ Real.exp (2 * (12 / 625)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (12 / 625)) (129893351 / 125000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((193 / 10000) : ℝ)) ≤ (1039354659 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (193 / 10000)) (1039354659 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((12955637 / 500000) : ℝ) ≤ Real.exp ((3264479 / 1000000) - (193 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3264479 / 1000000) - (193 / 10000) / 2) (12955637 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (12 / 625) (193 / 10000) (129893351 / 125000000) (1039354659 / 1000000000)
    (3264479 / 1000000) (3265237 / 1000000) (12955637 / 500000) (192966197 / 5000000000) (-443583 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell193 :
    ∀ u : ℝ, u ∈ Set.Icc ((193 / 10000) : ℝ) (97 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((519677329 / 500000000) : ℝ) ≤ Real.exp (2 * (193 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (193 / 10000)) (519677329 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((97 / 5000) : ℝ)) ≤ (1039562551 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (97 / 5000)) (1039562551 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((1620431 / 62500) : ℝ) ≤ Real.exp ((816283 / 250000) - (97 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((816283 / 250000) - (97 / 5000) / 2) (1620431 / 62500) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (193 / 10000) (97 / 5000) (519677329 / 500000000) (1039562551 / 1000000000)
    (816283 / 250000) (326589 / 100000) (1620431 / 62500) (192849927 / 5000000000) (-110947 / 250) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell194 :
    ∀ u : ℝ, u ∈ Set.Icc ((97 / 5000) : ℝ) (39 / 2000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((20791251 / 20000000) : ℝ) ≤ Real.exp (2 * (97 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (97 / 5000)) (20791251 / 20000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((39 / 2000) : ℝ)) ≤ (259942621 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (39 / 2000)) (259942621 / 250000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((405352 / 15625) : ℝ) ≤ Real.exp ((653157 / 200000) - (39 / 2000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((653157 / 200000) - (39 / 2000) / 2) (405352 / 15625) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (97 / 5000) (39 / 2000) (20791251 / 20000000) (259942621 / 250000000)
    (653157 / 200000) (3266543 / 1000000) (405352 / 15625) (192733723 / 5000000000) (-443993 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell195 :
    ∀ u : ℝ, u ∈ Set.Icc ((39 / 2000) : ℝ) (49 / 2500) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1039770483 / 1000000000) : ℝ) ≤ Real.exp (2 * (39 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (39 / 2000)) (1039770483 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((49 / 2500) : ℝ)) ≤ (1039978459 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (49 / 2500)) (1039978459 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((2595817 / 100000) : ℝ) ≤ Real.exp ((1633219 / 500000) - (49 / 2500) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1633219 / 500000) - (49 / 2500) / 2) (2595817 / 100000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (39 / 2000) (49 / 2500) (1039770483 / 1000000000) (1039978459 / 1000000000)
    (1633219 / 500000) (3267197 / 1000000) (2595817 / 100000) (385235169 / 10000000000) (-444199 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell196 :
    ∀ u : ℝ, u ∈ Set.Icc ((49 / 2500) : ℝ) (197 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((519989229 / 500000000) : ℝ) ≤ Real.exp (2 * (49 / 2500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (49 / 2500)) (519989229 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((197 / 10000) : ℝ)) ≤ (260046619 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (197 / 10000)) (260046619 / 250000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25973847 / 1000000) : ℝ) ≤ Real.exp ((816773 / 250000) - (197 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((816773 / 250000) - (197 / 10000) / 2) (25973847 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (49 / 2500) (197 / 10000) (519989229 / 500000000) (260046619 / 250000000)
    (816773 / 250000) (65357 / 20000) (25973847 / 1000000) (385002653 / 10000000000) (-111101 / 250) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell197 :
    ∀ u : ℝ, u ∈ Set.Icc ((197 / 10000) : ℝ) (99 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((41607459 / 40000000) : ℝ) ≤ Real.exp (2 * (197 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (197 / 10000)) (41607459 / 40000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((99 / 5000) : ℝ)) ≤ (520197267 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (99 / 5000)) (520197267 / 500000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25989507 / 1000000) : ℝ) ≤ Real.exp ((653549 / 200000) - (99 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((653549 / 200000) - (99 / 5000) / 2) (25989507 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (197 / 10000) (99 / 5000) (41607459 / 40000000) (520197267 / 500000000)
    (653549 / 200000) (408563 / 125000) (25989507 / 1000000) (38477067 / 1000000000) (-444609 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell198 :
    ∀ u : ℝ, u ∈ Set.Icc ((99 / 5000) : ℝ) (199 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1040394533 / 1000000000) : ℝ) ≤ Real.exp (2 * (99 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (99 / 5000)) (1040394533 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((199 / 10000) : ℝ)) ≤ (1040602633 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (199 / 10000)) (1040602633 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((26005203 / 1000000) : ℝ) ≤ Real.exp ((3268399 / 1000000) - (199 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3268399 / 1000000) - (199 / 10000) / 2) (26005203 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (99 / 5000) (199 / 10000) (1040394533 / 1000000000) (1040602633 / 1000000000)
    (3268399 / 1000000) (1634579 / 500000) (26005203 / 1000000) (384538433 / 10000000000) (-222407 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell199 :
    ∀ u : ℝ, u ∈ Set.Icc ((199 / 10000) : ℝ) (1 / 50) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((130075329 / 125000000) : ℝ) ≤ Real.exp (2 * (199 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (199 / 10000)) (130075329 / 125000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((1 / 50) : ℝ)) ≤ (41632431 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1 / 50)) (41632431 / 40000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((6505227 / 250000) : ℝ) ≤ Real.exp ((3269053 / 1000000) - (1 / 50) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3269053 / 1000000) - (1 / 50) / 2) (6505227 / 250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (199 / 10000) (1 / 50) (130075329 / 125000000) (41632431 / 40000000)
    (3269053 / 1000000) (817453 / 250000) (6505227 / 250000) (48038293 / 1250000000) (-445019 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cellsBatch019 :
    ∀ u : ℝ, u ∈ Set.Icc ((19 / 1000) : ℝ) (1 / 50) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  exact (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell190
      hpThetaCNV_secondDerivative_cell191)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell192
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell193
      hpThetaCNV_secondDerivative_cell194)))
      (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell195
      hpThetaCNV_secondDerivative_cell196)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell197
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell198
      hpThetaCNV_secondDerivative_cell199))))

#print axioms hpThetaCNV_secondDerivative_cellsBatch019
end HodgeProofHP
