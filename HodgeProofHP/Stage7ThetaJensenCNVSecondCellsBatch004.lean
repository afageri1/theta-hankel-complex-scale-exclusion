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

theorem hpThetaCNV_secondDerivative_cell040 :
    ∀ u : ℝ, u ∈ Set.Icc ((1 / 250) : ℝ) (41 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((201606417 / 200000000) : ℝ) ≤ Real.exp (2 * (1 / 250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1 / 250)) (201606417 / 200000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((41 / 10000) : ℝ)) ≤ (1008233713 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41 / 10000)) (1008233713 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((11839223 / 500000) : ℝ) ≤ Real.exp ((791683 / 250000) - (41 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((791683 / 250000) - (41 / 10000) / 2) (11839223 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (1 / 250) (41 / 10000) (201606417 / 200000000) (1008233713 / 1000000000)
    (791683 / 250000) (791867 / 250000) (11839223 / 500000) (422325013 / 10000000000) (-412059 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell041 :
    ∀ u : ℝ, u ∈ Set.Icc ((41 / 10000) : ℝ) (21 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((63014607 / 62500000) : ℝ) ≤ Real.exp (2 * (41 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41 / 10000)) (63014607 / 62500000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((21 / 5000) : ℝ)) ≤ (1008435379 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (21 / 5000)) (1008435379 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((23692273 / 1000000) : ℝ) ≤ Real.exp ((1583683 / 500000) - (21 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1583683 / 500000) - (21 / 5000) / 2) (23692273 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (41 / 10000) (21 / 5000) (63014607 / 62500000) (1008435379 / 1000000000)
    (1583683 / 500000) (3168101 / 1000000) (23692273 / 1000000) (422078541 / 10000000000) (-103067 / 250) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell042 :
    ∀ u : ℝ, u ∈ Set.Icc ((21 / 5000) : ℝ) (43 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((504217689 / 500000000) : ℝ) ≤ Real.exp (2 * (21 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (21 / 5000)) (504217689 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((43 / 10000) : ℝ)) ≤ (1008637087 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43 / 10000)) (1008637087 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((4741217 / 200000) : ℝ) ≤ Real.exp ((3167999 / 1000000) - (43 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3167999 / 1000000) - (43 / 10000) / 2) (4741217 / 200000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (21 / 5000) (43 / 10000) (504217689 / 500000000) (1008637087 / 1000000000)
    (3167999 / 1000000) (633747 / 200000) (4741217 / 200000) (421832623 / 10000000000) (-412477 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell043 :
    ∀ u : ℝ, u ∈ Set.Icc ((43 / 10000) : ℝ) (11 / 2500) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((504318543 / 500000000) : ℝ) ≤ Real.exp (2 * (43 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43 / 10000)) (504318543 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((11 / 2500) : ℝ)) ≤ (504419417 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (11 / 2500)) (504419417 / 500000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((23719929 / 1000000) : ℝ) ≤ Real.exp ((3168633 / 1000000) - (11 / 2500) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3168633 / 1000000) - (11 / 2500) / 2) (23719929 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (43 / 10000) (11 / 2500) (504318543 / 500000000) (504419417 / 500000000)
    (3168633 / 1000000) (3169369 / 1000000) (23719929 / 1000000) (421586423 / 10000000000) (-82537 / 200) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell044 :
    ∀ u : ℝ, u ∈ Set.Icc ((11 / 2500) : ℝ) (9 / 2000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1008838833 / 1000000000) : ℝ) ≤ Real.exp (2 * (11 / 2500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (11 / 2500)) (1008838833 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((9 / 2000) : ℝ)) ≤ (504520311 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9 / 2000)) (504520311 / 500000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((23733781 / 1000000) : ℝ) ≤ Real.exp ((3169267 / 1000000) - (9 / 2000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3169267 / 1000000) - (9 / 2000) / 2) (23733781 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (11 / 2500) (9 / 2000) (1008838833 / 1000000000) (504520311 / 500000000)
    (3169267 / 1000000) (3170003 / 1000000) (23733781 / 1000000) (26333773 / 625000000) (-206447 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell045 :
    ∀ u : ℝ, u ∈ Set.Icc ((9 / 2000) : ℝ) (23 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1009040621 / 1000000000) : ℝ) ≤ Real.exp (2 * (9 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9 / 2000)) (1009040621 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((23 / 5000) : ℝ)) ≤ (1009242451 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (23 / 5000)) (1009242451 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((23747641 / 1000000) : ℝ) ≤ Real.exp ((3169901 / 1000000) - (23 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3169901 / 1000000) - (23 / 5000) / 2) (23747641 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (9 / 2000) (23 / 5000) (1009040621 / 1000000000) (1009242451 / 1000000000)
    (3169901 / 1000000) (3170637 / 1000000) (23747641 / 1000000) (210547229 / 5000000000) (-413103 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell046 :
    ∀ u : ℝ, u ∈ Set.Icc ((23 / 5000) : ℝ) (47 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((20184849 / 20000000) : ℝ) ≤ Real.exp (2 * (23 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (23 / 5000)) (20184849 / 20000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((47 / 10000) : ℝ)) ≤ (1009444319 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (47 / 10000)) (1009444319 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((23761509 / 1000000) : ℝ) ≤ Real.exp ((634107 / 200000) - (47 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((634107 / 200000) - (47 / 10000) / 2) (23761509 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (23 / 5000) (47 / 10000) (20184849 / 20000000) (1009444319 / 1000000000)
    (634107 / 200000) (3171271 / 1000000) (23761509 / 1000000) (420848693 / 10000000000) (-413311 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell047 :
    ∀ u : ℝ, u ∈ Set.Icc ((47 / 10000) : ℝ) (3 / 625) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((504722159 / 500000000) : ℝ) ≤ Real.exp (2 * (47 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (47 / 10000)) (504722159 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((3 / 625) : ℝ)) ≤ (252411557 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3 / 625)) (252411557 / 250000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((4755077 / 200000) : ℝ) ≤ Real.exp ((3171169 / 1000000) - (3 / 625) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3171169 / 1000000) - (3 / 625) / 2) (4755077 / 200000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (47 / 10000) (3 / 625) (504722159 / 500000000) (252411557 / 250000000)
    (3171169 / 1000000) (634381 / 200000) (4755077 / 200000) (210301537 / 5000000000) (-10338 / 25) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell048 :
    ∀ u : ℝ, u ∈ Set.Icc ((3 / 625) : ℝ) (49 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1009646227 / 1000000000) : ℝ) ≤ Real.exp (2 * (3 / 625)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3 / 625)) (1009646227 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((49 / 10000) : ℝ)) ≤ (504924089 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (49 / 10000)) (504924089 / 500000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((23789269 / 1000000) : ℝ) ≤ Real.exp ((3171803 / 1000000) - (49 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3171803 / 1000000) - (49 / 10000) / 2) (23789269 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (3 / 625) (49 / 10000) (1009646227 / 1000000000) (504924089 / 500000000)
    (3171803 / 1000000) (158627 / 50000) (23789269 / 1000000) (525447 / 12500000) (-413729 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell049 :
    ∀ u : ℝ, u ∈ Set.Icc ((49 / 10000) : ℝ) (1 / 200) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1009848177 / 1000000000) : ℝ) ≤ Real.exp (2 * (49 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (49 / 10000)) (1009848177 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((1 / 200) : ℝ)) ≤ (126256271 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1 / 200)) (126256271 / 125000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((4760637 / 200000) : ℝ) ≤ Real.exp ((1586219 / 500000) - (1 / 200) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1586219 / 500000) - (1 / 200) / 2) (4760637 / 200000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (49 / 10000) (1 / 200) (1009848177 / 1000000000) (126256271 / 125000000)
    (1586219 / 500000) (1586587 / 500000) (4760637 / 200000) (420111847 / 10000000000) (-413937 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cellsBatch004 :
    ∀ u : ℝ, u ∈ Set.Icc ((1 / 250) : ℝ) (1 / 200) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  exact (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell040
      hpThetaCNV_secondDerivative_cell041)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell042
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell043
      hpThetaCNV_secondDerivative_cell044)))
      (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell045
      hpThetaCNV_secondDerivative_cell046)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell047
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell048
      hpThetaCNV_secondDerivative_cell049))))

#print axioms hpThetaCNV_secondDerivative_cellsBatch004
end HodgeProofHP
