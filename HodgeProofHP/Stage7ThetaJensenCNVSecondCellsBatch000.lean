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

theorem hpThetaCNV_secondDerivative_cell000 :
    ∀ u : ℝ, u ∈ Set.Icc (0 : ℝ) (1 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : (1 : ℝ) ≤ Real.exp (2 * 0) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * 0) 1 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((1 / 10000) : ℝ)) ≤ (1000200021 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1 / 10000)) (1000200021 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((4626973 / 200000) : ℝ) ≤ Real.exp ((6283 / 2000) - (1 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((6283 / 2000) - (1 / 10000) / 2) (4626973 / 200000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    0 (1 / 10000) 1 (1000200021 / 1000000000)
    (6283 / 2000) (3142229 / 1000000) (4626973 / 200000) (216124019 / 5000000000) (-403703 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell001 :
    ∀ u : ℝ, u ∈ Set.Icc ((1 / 10000) : ℝ) (1 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((50010001 / 50000000) : ℝ) ≤ Real.exp (2 * (1 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1 / 10000)) (50010001 / 50000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((1 / 5000) : ℝ)) ≤ (1000400081 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1 / 5000)) (1000400081 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((23148237 / 1000000) : ℝ) ≤ Real.exp ((196383 / 62500) - (1 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((196383 / 62500) - (1 / 5000) / 2) (23148237 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (1 / 10000) (1 / 5000) (50010001 / 50000000) (1000400081 / 1000000000)
    (196383 / 62500) (3142857 / 1000000) (23148237 / 1000000) (215999171 / 5000000000) (-50489 / 125) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell002 :
    ∀ u : ℝ, u ∈ Set.Icc ((1 / 5000) : ℝ) (3 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((12505001 / 12500000) : ℝ) ≤ Real.exp (2 * (1 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1 / 5000)) (12505001 / 12500000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((3 / 10000) : ℝ)) ≤ (1000600181 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3 / 10000)) (1000600181 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((1447601 / 62500) : ℝ) ≤ Real.exp ((785689 / 250000) - (3 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((785689 / 250000) - (3 / 10000) / 2) (1447601 / 62500) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (1 / 5000) (3 / 10000) (12505001 / 12500000) (1000600181 / 1000000000)
    (785689 / 250000) (1571743 / 500000) (1447601 / 62500) (107937201 / 2500000000) (-404121 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell003 :
    ∀ u : ℝ, u ∈ Set.Icc ((3 / 10000) : ℝ) (1 / 2500) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((50030009 / 50000000) : ℝ) ≤ Real.exp (2 * (3 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3 / 10000)) (50030009 / 50000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((1 / 2500) : ℝ)) ≤ (1000800321 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1 / 2500)) (1000800321 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((11587513 / 500000) : ℝ) ≤ Real.exp ((628677 / 200000) - (1 / 2500) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((628677 / 200000) - (1 / 2500) / 2) (11587513 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (3 / 10000) (1 / 2500) (50030009 / 50000000) (1000800321 / 1000000000)
    (628677 / 200000) (628823 / 200000) (11587513 / 500000) (431498977 / 10000000000) (-40433 / 100) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell004 :
    ∀ u : ℝ, u ∈ Set.Icc ((1 / 2500) : ℝ) (1 / 2000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((3127501 / 3125000) : ℝ) ≤ Real.exp (2 * (1 / 2500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1 / 2500)) (3127501 / 3125000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((1 / 2000) : ℝ)) ≤ (1001000501 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1 / 2000)) (1001000501 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((5797111 / 250000) : ℝ) ≤ Real.exp ((1572007 / 500000) - (1 / 2000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1572007 / 500000) - (1 / 2000) / 2) (5797111 / 250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (1 / 2500) (1 / 2000) (3127501 / 3125000) (1001000501 / 1000000000)
    (1572007 / 500000) (393093 / 125000) (5797111 / 250000) (43124929 / 1000000000) (-404539 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell005 :
    ∀ u : ℝ, u ∈ Set.Icc ((1 / 2000) : ℝ) (3 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((2002001 / 2000000) : ℝ) ≤ Real.exp (2 * (1 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1 / 2000)) (2002001 / 2000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((3 / 5000) : ℝ)) ≤ (1001200721 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3 / 5000)) (1001200721 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((2320187 / 100000) : ℝ) ≤ Real.exp ((3144643 / 1000000) - (3 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3144643 / 1000000) - (3 / 5000) / 2) (2320187 / 100000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (1 / 2000) (3 / 5000) (2002001 / 2000000) (1001200721 / 1000000000)
    (3144643 / 1000000) (3145373 / 1000000) (2320187 / 100000) (430999743 / 10000000000) (-101187 / 250) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell006 :
    ∀ u : ℝ, u ∈ Set.Icc ((3 / 5000) : ℝ) (7 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((12515009 / 12500000) : ℝ) ≤ Real.exp (2 * (3 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3 / 5000)) (12515009 / 12500000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((7 / 10000) : ℝ)) ≤ (1001400981 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (7 / 10000)) (1001400981 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((23215303 / 1000000) : ℝ) ≤ Real.exp ((393159 / 125000) - (7 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((393159 / 125000) - (7 / 10000) / 2) (23215303 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (3 / 5000) (7 / 10000) (12515009 / 12500000) (1001400981 / 1000000000)
    (393159 / 125000) (1573001 / 500000) (23215303 / 1000000) (86150071 / 2000000000) (-404957 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell007 :
    ∀ u : ℝ, u ∈ Set.Icc ((7 / 10000) : ℝ) (1 / 1250) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((50070049 / 50000000) : ℝ) ≤ Real.exp (2 * (7 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (7 / 10000)) (50070049 / 50000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((1 / 1250) : ℝ)) ≤ (1001601281 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1 / 1250)) (1001601281 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((2903593 / 125000) : ℝ) ≤ Real.exp ((3145901 / 1000000) - (1 / 1250) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3145901 / 1000000) - (1 / 1250) / 2) (2903593 / 125000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (7 / 10000) (1 / 1250) (50070049 / 50000000) (1001601281 / 1000000000)
    (3145901 / 1000000) (3146631 / 1000000) (2903593 / 125000) (430501107 / 10000000000) (-202583 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell008 :
    ∀ u : ℝ, u ∈ Set.Icc ((1 / 1250) : ℝ) (9 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((782501 / 781250) : ℝ) ≤ Real.exp (2 * (1 / 1250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1 / 1250)) (782501 / 781250) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((9 / 10000) : ℝ)) ≤ (1001801621 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9 / 10000)) (1001801621 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((23242193 / 1000000) : ℝ) ≤ Real.exp ((314653 / 100000) - (9 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((314653 / 100000) - (9 / 10000) / 2) (23242193 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (1 / 1250) (9 / 10000) (782501 / 781250) (1001801621 / 1000000000)
    (314653 / 100000) (157363 / 50000) (23242193 / 1000000) (107563 / 2500000) (-3243 / 8) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell009 :
    ∀ u : ℝ, u ∈ Set.Icc ((9 / 10000) : ℝ) (1 / 1000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((50090081 / 50000000) : ℝ) ≤ Real.exp (2 * (9 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9 / 10000)) (50090081 / 50000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((1 / 1000) : ℝ)) ≤ (501001001 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1 / 1000)) (501001001 / 500000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((465113 / 20000) : ℝ) ≤ Real.exp ((3147159 / 1000000) - (1 / 1000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3147159 / 1000000) - (1 / 1000) / 2) (465113 / 20000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (9 / 10000) (1 / 1000) (50090081 / 50000000) (501001001 / 500000000)
    (3147159 / 1000000) (314789 / 100000) (465113 / 20000) (53750379 / 1250000000) (-50698 / 125) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cellsBatch000 :
    ∀ u : ℝ, u ∈ Set.Icc (0 : ℝ) (1 / 1000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  exact (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell000
      hpThetaCNV_secondDerivative_cell001)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell002
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell003
      hpThetaCNV_secondDerivative_cell004)))
      (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell005
      hpThetaCNV_secondDerivative_cell006)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell007
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell008
      hpThetaCNV_secondDerivative_cell009))))

#print axioms hpThetaCNV_secondDerivative_cellsBatch000
end HodgeProofHP
