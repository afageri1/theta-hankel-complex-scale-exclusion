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

theorem hpThetaCNV_secondDerivative_cell140 :
    ∀ u : ℝ, u ∈ Set.Icc ((7 / 500) : ℝ) (141 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((257098921 / 250000000) : ℝ) ≤ Real.exp (2 * (7 / 500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (7 / 500)) (257098921 / 250000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((141 / 10000) : ℝ)) ≤ (205720277 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (141 / 10000)) (205720277 / 200000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25116293 / 1000000) : ℝ) ≤ Real.exp ((646141 / 200000) - (141 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((646141 / 200000) - (141 / 10000) / 2) (25116293 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (7 / 500) (141 / 10000) (257098921 / 250000000) (205720277 / 200000000)
    (646141 / 200000) (646291 / 200000) (25116293 / 1000000) (49768491 / 1250000000) (-21643 / 50) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell141 :
    ∀ u : ℝ, u ∈ Set.Icc ((141 / 10000) : ℝ) (71 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((128575173 / 125000000) : ℝ) ≤ Real.exp (2 * (141 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (141 / 10000)) (128575173 / 125000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((71 / 5000) : ℝ)) ≤ (8230457 / 8000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (71 / 5000)) (8230457 / 8000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25131261 / 1000000) : ℝ) ≤ Real.exp ((3231351 / 1000000) - (71 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3231351 / 1000000) - (71 / 5000) / 2) (25131261 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (141 / 10000) (71 / 5000) (128575173 / 125000000) (8230457 / 8000000)
    (3231351 / 1000000) (3232101 / 1000000) (25131261 / 1000000) (198955397 / 5000000000) (-433067 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell142 :
    ∀ u : ℝ, u ∈ Set.Icc ((71 / 5000) : ℝ) (143 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((257201781 / 250000000) : ℝ) ≤ Real.exp (2 * (71 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (71 / 5000)) (257201781 / 250000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((143 / 10000) : ℝ)) ≤ (1029012907 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (143 / 10000)) (1029012907 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((12573119 / 500000) : ℝ) ≤ Real.exp ((3231997 / 1000000) - (143 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3231997 / 1000000) - (143 / 10000) / 2) (12573119 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (71 / 5000) (143 / 10000) (257201781 / 250000000) (1029012907 / 1000000000)
    (3231997 / 1000000) (3232747 / 1000000) (12573119 / 500000) (1988369 / 50000000) (-216637 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell143 :
    ∀ u : ℝ, u ∈ Set.Icc ((143 / 10000) : ℝ) (9 / 625) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((514506453 / 500000000) : ℝ) ≤ Real.exp (2 * (143 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (143 / 10000)) (514506453 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((9 / 625) : ℝ)) ≤ (1029218731 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9 / 625)) (1029218731 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25161249 / 1000000) : ℝ) ≤ Real.exp ((808161 / 250000) - (9 / 625) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((808161 / 250000) - (9 / 625) / 2) (25161249 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (143 / 10000) (9 / 625) (514506453 / 500000000) (1029218731 / 1000000000)
    (808161 / 250000) (1616697 / 500000) (25161249 / 1000000) (397436551 / 10000000000) (-433481 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell144 :
    ∀ u : ℝ, u ∈ Set.Icc ((9 / 625) : ℝ) (29 / 2000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((102921873 / 100000000) : ℝ) ≤ Real.exp (2 * (9 / 625)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9 / 625)) (102921873 / 100000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((29 / 2000) : ℝ)) ≤ (205884919 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (29 / 2000)) (205884919 / 200000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25176243 / 1000000) : ℝ) ≤ Real.exp ((323329 / 100000) - (29 / 2000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((323329 / 100000) - (29 / 2000) / 2) (25176243 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (9 / 625) (29 / 2000) (102921873 / 100000000) (205884919 / 200000000)
    (323329 / 100000) (3234041 / 1000000) (25176243 / 1000000) (397199853 / 10000000000) (-54211 / 125) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell145 :
    ∀ u : ℝ, u ∈ Set.Icc ((29 / 2000) : ℝ) (73 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((514712297 / 500000000) : ℝ) ≤ Real.exp (2 * (29 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (29 / 2000)) (514712297 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((73 / 5000) : ℝ)) ≤ (2059261 / 2000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (73 / 5000)) (2059261 / 2000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((3148909 / 125000) : ℝ) ≤ Real.exp ((3233937 / 1000000) - (73 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3233937 / 1000000) - (73 / 5000) / 2) (3148909 / 125000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (29 / 2000) (73 / 5000) (514712297 / 500000000) (2059261 / 2000000)
    (3233937 / 1000000) (50542 / 15625) (3148909 / 125000) (79392577 / 2000000000) (-86779 / 200) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell146 :
    ∀ u : ℝ, u ∈ Set.Icc ((73 / 5000) : ℝ) (147 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1029630499 / 1000000000) : ℝ) ≤ Real.exp (2 * (73 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (73 / 5000)) (1029630499 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((147 / 10000) : ℝ)) ≤ (1029836447 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (147 / 10000)) (1029836447 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((2520631 / 100000) : ℝ) ≤ Real.exp ((404323 / 125000) - (147 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((404323 / 125000) - (147 / 10000) / 2) (2520631 / 100000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (73 / 5000) (147 / 10000) (1029630499 / 1000000000) (1029836447 / 1000000000)
    (404323 / 125000) (647067 / 200000) (2520631 / 100000) (198363029 / 5000000000) (-217051 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell147 :
    ∀ u : ℝ, u ∈ Set.Icc ((147 / 10000) : ℝ) (37 / 2500) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((514918223 / 500000000) : ℝ) ≤ Real.exp (2 * (147 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (147 / 10000)) (514918223 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((37 / 2500) : ℝ)) ≤ (206008487 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (37 / 2500)) (206008487 / 200000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25221357 / 1000000) : ℝ) ≤ Real.exp ((3235231 / 1000000) - (37 / 2500) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3235231 / 1000000) - (37 / 2500) / 2) (25221357 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (147 / 10000) (37 / 2500) (514918223 / 500000000) (206008487 / 200000000)
    (3235231 / 1000000) (1617991 / 500000) (25221357 / 1000000) (396489373 / 10000000000) (-108577 / 250) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell148 :
    ∀ u : ℝ, u ∈ Set.Icc ((37 / 2500) : ℝ) (149 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((515021217 / 500000000) : ℝ) ≤ Real.exp (2 * (37 / 2500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (37 / 2500)) (515021217 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((149 / 10000) : ℝ)) ≤ (64390529 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (149 / 10000)) (64390529 / 62500000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25236413 / 1000000) : ℝ) ≤ Real.exp ((1617939 / 500000) - (149 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1617939 / 500000) - (149 / 10000) / 2) (25236413 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (37 / 2500) (149 / 10000) (515021217 / 500000000) (64390529 / 62500000)
    (1617939 / 500000) (3236629 / 1000000) (25236413 / 1000000) (99063207 / 2500000000) (-86903 / 200) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell149 :
    ∀ u : ℝ, u ∈ Set.Icc ((149 / 10000) : ℝ) (3 / 200) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1030248463 / 1000000000) : ℝ) ≤ Real.exp (2 * (149 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (149 / 10000)) (1030248463 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((3 / 200) : ℝ)) ≤ (515227267 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3 / 200)) (515227267 / 500000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25251477 / 1000000) : ℝ) ≤ Real.exp ((129461 / 40000) - (3 / 200) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((129461 / 40000) - (3 / 200) / 2) (25251477 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (149 / 10000) (3 / 200) (1030248463 / 1000000000) (515227267 / 500000000)
    (129461 / 40000) (809319 / 250000) (25251477 / 1000000) (396016439 / 10000000000) (-217361 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cellsBatch014 :
    ∀ u : ℝ, u ∈ Set.Icc ((7 / 500) : ℝ) (3 / 200) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  exact (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell140
      hpThetaCNV_secondDerivative_cell141)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell142
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell143
      hpThetaCNV_secondDerivative_cell144)))
      (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell145
      hpThetaCNV_secondDerivative_cell146)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell147
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell148
      hpThetaCNV_secondDerivative_cell149))))

#print axioms hpThetaCNV_secondDerivative_cellsBatch014
end HodgeProofHP
