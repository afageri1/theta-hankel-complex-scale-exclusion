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

theorem hpThetaCNV_secondDerivative_cell070 :
    ∀ u : ℝ, u ∈ Set.Icc ((7 / 1000) : ℝ) (71 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((507049229 / 500000000) : ℝ) ≤ Real.exp (2 * (7 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (7 / 1000)) (507049229 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((71 / 10000) : ℝ)) ≤ (1014301299 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (71 / 10000)) (1014301299 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((24097717 / 1000000) : ℝ) ≤ Real.exp ((318579 / 100000) - (71 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((318579 / 100000) - (71 / 10000) / 2) (24097717 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (7 / 1000) (71 / 10000) (507049229 / 500000000) (1014301299 / 1000000000)
    (318579 / 100000) (3186529 / 1000000) (24097717 / 1000000) (414977071 / 10000000000) (-418317 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell071 :
    ∀ u : ℝ, u ∈ Set.Icc ((71 / 10000) : ℝ) (9 / 1250) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((507150649 / 500000000) : ℝ) ≤ Real.exp (2 * (71 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (71 / 10000)) (507150649 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((9 / 1250) : ℝ)) ≤ (50725209 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9 / 1250)) (50725209 / 50000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((12055931 / 500000) : ℝ) ≤ Real.exp ((3186427 / 1000000) - (9 / 1250) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3186427 / 1000000) - (9 / 1250) / 2) (12055931 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (71 / 10000) (9 / 1250) (507150649 / 500000000) (50725209 / 50000000)
    (3186427 / 1000000) (3187167 / 1000000) (12055931 / 500000) (103683407 / 2500000000) (-16741 / 40) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell072 :
    ∀ u : ℝ, u ∈ Set.Icc ((9 / 1250) : ℝ) (73 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1014504179 / 1000000000) : ℝ) ≤ Real.exp (2 * (9 / 1250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9 / 1250)) (1014504179 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((73 / 10000) : ℝ)) ≤ (1014707101 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (73 / 10000)) (1014707101 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((4825203 / 200000) : ℝ) ≤ Real.exp ((398383 / 125000) - (73 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((398383 / 125000) - (73 / 10000) / 2) (4825203 / 200000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (9 / 1250) (73 / 10000) (1014504179 / 1000000000) (1014707101 / 1000000000)
    (398383 / 125000) (796951 / 250000) (4825203 / 200000) (207245167 / 5000000000) (-418733 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell073 :
    ∀ u : ℝ, u ∈ Set.Icc ((73 / 10000) : ℝ) (37 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((10147071 / 10000000) : ℝ) ≤ Real.exp (2 * (73 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (73 / 10000)) (10147071 / 10000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((37 / 5000) : ℝ)) ≤ (1014910063 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (37 / 5000)) (1014910063 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((120701 / 5000) : ℝ) ≤ Real.exp ((1593851 / 500000) - (37 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1593851 / 500000) - (37 / 5000) / 2) (120701 / 5000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (73 / 10000) (37 / 5000) (10147071 / 10000000) (1014910063 / 1000000000)
    (1593851 / 500000) (1594221 / 500000) (120701 / 5000) (51780847 / 1250000000) (-209471 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell074 :
    ∀ u : ℝ, u ∈ Set.Icc ((37 / 5000) : ℝ) (3 / 400) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((507455031 / 500000000) : ℝ) ≤ Real.exp (2 * (37 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (37 / 5000)) (507455031 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((3 / 400) : ℝ)) ≤ (203022613 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3 / 400)) (203022613 / 200000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((24154369 / 1000000) : ℝ) ≤ Real.exp ((3188339 / 1000000) - (3 / 400) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3188339 / 1000000) - (3 / 400) / 2) (24154369 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (37 / 5000) (3 / 400) (507455031 / 500000000) (203022613 / 200000000)
    (3188339 / 1000000) (79727 / 25000) (24154369 / 1000000) (207001889 / 5000000000) (-8383 / 20) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell075 :
    ∀ u : ℝ, u ∈ Set.Icc ((3 / 400) : ℝ) (19 / 2500) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((126889133 / 125000000) : ℝ) ≤ Real.exp (2 * (3 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3 / 400)) (126889133 / 125000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((19 / 2500) : ℝ)) ≤ (253829027 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (19 / 2500)) (253829027 / 250000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((24168571 / 1000000) : ℝ) ≤ Real.exp ((3188977 / 1000000) - (19 / 2500) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3188977 / 1000000) - (19 / 2500) / 2) (24168571 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (3 / 400) (19 / 2500) (126889133 / 125000000) (253829027 / 250000000)
    (3188977 / 1000000) (1594859 / 500000) (24168571 / 1000000) (827521 / 20000000) (-419359 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell076 :
    ∀ u : ℝ, u ∈ Set.Icc ((19 / 2500) : ℝ) (77 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1015316107 / 1000000000) : ℝ) ≤ Real.exp (2 * (19 / 2500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (19 / 2500)) (1015316107 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((77 / 10000) : ℝ)) ≤ (126939899 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (77 / 10000)) (126939899 / 125000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((24182781 / 1000000) : ℝ) ≤ Real.exp ((637923 / 200000) - (77 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((637923 / 200000) - (77 / 10000) / 2) (24182781 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (19 / 2500) (77 / 10000) (1015316107 / 1000000000) (126939899 / 125000000)
    (637923 / 200000) (797589 / 250000) (24182781 / 1000000) (413517371 / 10000000000) (-419567 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell077 :
    ∀ u : ℝ, u ∈ Set.Icc ((77 / 10000) : ℝ) (39 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1015519191 / 1000000000) : ℝ) ≤ Real.exp (2 * (77 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (77 / 10000)) (1015519191 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((39 / 5000) : ℝ)) ≤ (253930579 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (39 / 5000)) (253930579 / 250000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((24197 / 1000) : ℝ) ≤ Real.exp ((3190253 / 1000000) - (39 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3190253 / 1000000) - (39 / 5000) / 2) (24197 / 1000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (77 / 10000) (39 / 5000) (1015519191 / 1000000000) (253930579 / 250000000)
    (3190253 / 1000000) (1595497 / 500000) (24197 / 1000) (413274373 / 10000000000) (-16791 / 40) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell078 :
    ∀ u : ℝ, u ∈ Set.Icc ((39 / 5000) : ℝ) (79 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((203144463 / 200000000) : ℝ) ≤ Real.exp (2 * (39 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (39 / 5000)) (203144463 / 200000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((79 / 10000) : ℝ)) ≤ (25398137 / 25000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (79 / 10000)) (25398137 / 25000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((24211227 / 1000000) : ℝ) ≤ Real.exp ((3190891 / 1000000) - (79 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3190891 / 1000000) - (79 / 10000) / 2) (24211227 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (39 / 5000) (79 / 10000) (203144463 / 200000000) (25398137 / 25000000)
    (3190891 / 1000000) (199477 / 62500) (24211227 / 1000000) (16521261 / 400000000) (-52498 / 125) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell079 :
    ∀ u : ℝ, u ∈ Set.Icc ((79 / 10000) : ℝ) (1 / 125) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1015925479 / 1000000000) : ℝ) ≤ Real.exp (2 * (79 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (79 / 10000)) (1015925479 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((1 / 125) : ℝ)) ≤ (508064343 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1 / 125)) (508064343 / 500000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((12112731 / 500000) : ℝ) ≤ Real.exp ((3191529 / 1000000) - (1 / 125) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3191529 / 1000000) - (1 / 125) / 2) (12112731 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (79 / 10000) (1 / 125) (1015925479 / 1000000000) (508064343 / 500000000)
    (3191529 / 1000000) (319227 / 100000) (12112731 / 500000) (206394413 / 5000000000) (-52524 / 125) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cellsBatch007 :
    ∀ u : ℝ, u ∈ Set.Icc ((7 / 1000) : ℝ) (1 / 125) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  exact (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell070
      hpThetaCNV_secondDerivative_cell071)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell072
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell073
      hpThetaCNV_secondDerivative_cell074)))
      (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell075
      hpThetaCNV_secondDerivative_cell076)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell077
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell078
      hpThetaCNV_secondDerivative_cell079))))

#print axioms hpThetaCNV_secondDerivative_cellsBatch007
end HodgeProofHP
