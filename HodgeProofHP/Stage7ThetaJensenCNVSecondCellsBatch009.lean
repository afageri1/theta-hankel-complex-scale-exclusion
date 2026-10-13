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

theorem hpThetaCNV_secondDerivative_cell090 :
    ∀ u : ℝ, u ∈ Set.Icc ((9 / 1000) : ℝ) (91 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((31817593 / 31250000) : ℝ) ≤ Real.exp (2 * (9 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9 / 1000)) (31817593 / 31250000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((91 / 10000) : ℝ)) ≤ (101836663 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (91 / 10000)) (101836663 / 100000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((3047859 / 125000) : ℝ) ≤ Real.exp ((1599279 / 500000) - (91 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1599279 / 500000) - (91 / 10000) / 2) (3047859 / 125000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (9 / 1000) (91 / 10000) (31817593 / 31250000) (101836663 / 100000000)
    (1599279 / 500000) (3199301 / 1000000) (3047859 / 125000) (10253099 / 250000000) (-211241 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell091 :
    ∀ u : ℝ, u ∈ Set.Icc ((91 / 10000) : ℝ) (23 / 2500) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1018366629 / 1000000000) : ℝ) ≤ Real.exp (2 * (91 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (91 / 10000)) (1018366629 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((23 / 2500) : ℝ)) ≤ (254642581 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (23 / 2500)) (254642581 / 250000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((24397257 / 1000000) : ℝ) ≤ Real.exp ((1599599 / 500000) - (23 / 2500) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1599599 / 500000) - (23 / 2500) / 2) (24397257 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (91 / 10000) (23 / 2500) (1018366629 / 1000000000) (254642581 / 250000000)
    (1599599 / 500000) (3199941 / 1000000) (24397257 / 1000000) (12808817 / 312500000) (-42269 / 100) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell092 :
    ∀ u : ℝ, u ∈ Set.Icc ((23 / 2500) : ℝ) (93 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1018570323 / 1000000000) : ℝ) ≤ Real.exp (2 * (23 / 2500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (23 / 2500)) (1018570323 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((93 / 10000) : ℝ)) ≤ (509387029 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (93 / 10000)) (509387029 / 500000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((488233 / 20000) : ℝ) ≤ Real.exp ((1599919 / 500000) - (93 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1599919 / 500000) - (93 / 10000) / 2) (488233 / 20000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (23 / 2500) (93 / 10000) (1018570323 / 1000000000) (509387029 / 500000000)
    (1599919 / 500000) (3200581 / 1000000) (488233 / 20000) (2560253 / 62500000) (-211449 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell093 :
    ∀ u : ℝ, u ∈ Set.Icc ((93 / 10000) : ℝ) (47 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1018774057 / 1000000000) : ℝ) ≤ Real.exp (2 * (93 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (93 / 10000)) (1018774057 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((47 / 5000) : ℝ)) ≤ (1018977833 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (47 / 5000)) (1018977833 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((6106513 / 250000) : ℝ) ≤ Real.exp ((1600239 / 500000) - (47 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1600239 / 500000) - (47 / 5000) / 2) (6106513 / 250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (93 / 10000) (47 / 5000) (1018774057 / 1000000000) (1018977833 / 1000000000)
    (1600239 / 500000) (3201221 / 1000000) (6106513 / 250000) (409398949 / 10000000000) (-211553 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell094 :
    ∀ u : ℝ, u ∈ Set.Icc ((47 / 5000) : ℝ) (19 / 2000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((127372229 / 125000000) : ℝ) ≤ Real.exp (2 * (47 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (47 / 5000)) (127372229 / 125000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((19 / 2000) : ℝ)) ≤ (1019181649 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (19 / 2000)) (1019181649 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((12220231 / 500000) : ℝ) ≤ Real.exp ((1600559 / 500000) - (19 / 2000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1600559 / 500000) - (19 / 2000) / 2) (12220231 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (47 / 5000) (19 / 2000) (127372229 / 125000000) (1019181649 / 1000000000)
    (1600559 / 500000) (1600931 / 500000) (12220231 / 500000) (409157569 / 10000000000) (-211657 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell095 :
    ∀ u : ℝ, u ∈ Set.Icc ((19 / 2000) : ℝ) (6 / 625) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((63698853 / 62500000) : ℝ) ≤ Real.exp (2 * (19 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (19 / 2000)) (63698853 / 62500000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((6 / 625) : ℝ)) ≤ (509692753 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (6 / 625)) (509692753 / 500000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((12227453 / 500000) : ℝ) ≤ Real.exp ((3201759 / 1000000) - (6 / 625) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3201759 / 1000000) - (6 / 625) / 2) (12227453 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (19 / 2000) (6 / 625) (63698853 / 62500000) (509692753 / 500000000)
    (3201759 / 1000000) (1601251 / 500000) (12227453 / 500000) (81783181 / 2000000000) (-211761 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell096 :
    ∀ u : ℝ, u ∈ Set.Icc ((6 / 625) : ℝ) (97 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((203877101 / 200000000) : ℝ) ≤ Real.exp (2 * (6 / 625)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (6 / 625)) (203877101 / 200000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((97 / 10000) : ℝ)) ≤ (1019589403 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (97 / 10000)) (1019589403 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((24469333 / 1000000) : ℝ) ≤ Real.exp ((3202399 / 1000000) - (97 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3202399 / 1000000) - (97 / 10000) / 2) (24469333 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (6 / 625) (97 / 10000) (203877101 / 200000000) (1019589403 / 1000000000)
    (3202399 / 1000000) (3203143 / 1000000) (24469333 / 1000000) (40867481 / 1000000000) (-42373 / 100) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell097 :
    ∀ u : ℝ, u ∈ Set.Icc ((97 / 10000) : ℝ) (49 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((509794701 / 500000000) : ℝ) ≤ Real.exp (2 * (97 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (97 / 10000)) (509794701 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((49 / 5000) : ℝ)) ≤ (509896671 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (49 / 5000)) (509896671 / 500000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((24483793 / 1000000) : ℝ) ≤ Real.exp ((20019 / 6250) - (49 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((20019 / 6250) - (49 / 5000) / 2) (24483793 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (97 / 10000) (49 / 5000) (509794701 / 500000000) (509896671 / 500000000)
    (20019 / 6250) (3203783 / 1000000) (24483793 / 1000000) (408433449 / 10000000000) (-211969 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell098 :
    ∀ u : ℝ, u ∈ Set.Icc ((49 / 5000) : ℝ) (99 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1019793341 / 1000000000) : ℝ) ≤ Real.exp (2 * (49 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (49 / 5000)) (1019793341 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((99 / 10000) : ℝ)) ≤ (1019997321 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (99 / 10000)) (1019997321 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((12249119 / 500000) : ℝ) ≤ Real.exp ((20023 / 6250) - (99 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((20023 / 6250) - (99 / 10000) / 2) (12249119 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (49 / 5000) (99 / 10000) (1019793341 / 1000000000) (1019997321 / 1000000000)
    (20023 / 6250) (400553 / 125000) (12249119 / 500000) (204096311 / 5000000000) (-212073 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell099 :
    ∀ u : ℝ, u ∈ Set.Icc ((99 / 10000) : ℝ) (1 / 100) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((25499933 / 25000000) : ℝ) ≤ Real.exp (2 * (99 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (99 / 10000)) (25499933 / 25000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((1 / 100) : ℝ)) ≤ (1020201341 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1 / 100)) (1020201341 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((4902543 / 200000) : ℝ) ≤ Real.exp ((3204321 / 1000000) - (1 / 100) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3204321 / 1000000) - (1 / 100) / 2) (4902543 / 200000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (99 / 10000) (1 / 100) (25499933 / 25000000) (1020201341 / 1000000000)
    (3204321 / 1000000) (641013 / 200000) (4902543 / 200000) (407951547 / 10000000000) (-212177 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cellsBatch009 :
    ∀ u : ℝ, u ∈ Set.Icc ((9 / 1000) : ℝ) (1 / 100) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  exact (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell090
      hpThetaCNV_secondDerivative_cell091)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell092
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell093
      hpThetaCNV_secondDerivative_cell094)))
      (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell095
      hpThetaCNV_secondDerivative_cell096)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell097
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell098
      hpThetaCNV_secondDerivative_cell099))))

#print axioms hpThetaCNV_secondDerivative_cellsBatch009
end HodgeProofHP
