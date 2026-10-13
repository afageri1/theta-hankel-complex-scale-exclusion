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

theorem hpThetaCNV_secondDerivative_cell160 :
    ∀ u : ℝ, u ∈ Set.Icc ((2 / 125) : ℝ) (161 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((206503501 / 200000000) : ℝ) ≤ Real.exp (2 * (2 / 125)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2 / 125)) (206503501 / 200000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((161 / 10000) : ℝ)) ≤ (103272403 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (161 / 10000)) (103272403 / 100000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((12709031 / 500000) : ℝ) ≤ Real.exp ((3243653 / 1000000) - (161 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3243653 / 1000000) - (161 / 10000) / 2) (12709031 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (2 / 125) (161 / 10000) (206503501 / 200000000) (103272403 / 100000000)
    (3243653 / 1000000) (1622203 / 500000) (12709031 / 500000) (15736841 / 400000000) (-218497 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell161 :
    ∀ u : ℝ, u ∈ Set.Icc ((161 / 10000) : ℝ) (81 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1032724029 / 1000000000) : ℝ) ≤ Real.exp (2 * (161 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (161 / 10000)) (1032724029 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((81 / 5000) : ℝ)) ≤ (206586119 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (81 / 5000)) (206586119 / 200000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((12716643 / 500000) : ℝ) ≤ Real.exp ((1622151 / 500000) - (81 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1622151 / 500000) - (81 / 5000) / 2) (12716643 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (161 / 10000) (81 / 5000) (1032724029 / 1000000000) (206586119 / 200000000)
    (1622151 / 500000) (649011 / 200000) (12716643 / 500000) (393185529 / 10000000000) (-2186 / 5) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell162 :
    ∀ u : ℝ, u ∈ Set.Icc ((81 / 5000) : ℝ) (163 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((516465297 / 500000000) : ℝ) ≤ Real.exp (2 * (81 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (81 / 5000)) (516465297 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((163 / 10000) : ℝ)) ≤ (516568601 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (163 / 10000)) (516568601 / 500000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25448519 / 1000000) : ℝ) ≤ Real.exp ((3244951 / 1000000) - (163 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3244951 / 1000000) - (163 / 10000) / 2) (25448519 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (81 / 5000) (163 / 10000) (516465297 / 500000000) (516568601 / 500000000)
    (3244951 / 1000000) (405713 / 125000) (25448519 / 1000000) (12279693 / 312500000) (-437407 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell163 :
    ∀ u : ℝ, u ∈ Set.Icc ((163 / 10000) : ℝ) (41 / 2500) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1033137201 / 1000000000) : ℝ) ≤ Real.exp (2 * (163 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (163 / 10000)) (1033137201 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((41 / 2500) : ℝ)) ≤ (20666877 / 20000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41 / 2500)) (20666877 / 20000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25463761 / 1000000) : ℝ) ≤ Real.exp ((4057 / 1250) - (41 / 2500) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((4057 / 1250) - (41 / 2500) / 2) (25463761 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (163 / 10000) (41 / 2500) (1033137201 / 1000000000) (20666877 / 20000000)
    (4057 / 1250) (1623177 / 500000) (25463761 / 1000000) (78542993 / 2000000000) (-437613 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell164 :
    ∀ u : ℝ, u ∈ Set.Icc ((41 / 2500) : ℝ) (33 / 2000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1033343849 / 1000000000) : ℝ) ≤ Real.exp (2 * (41 / 2500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41 / 2500)) (1033343849 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((33 / 2000) : ℝ)) ≤ (51677527 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (33 / 2000)) (51677527 / 50000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25479013 / 1000000) : ℝ) ≤ Real.exp ((3246249 / 1000000) - (33 / 2000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3246249 / 1000000) - (33 / 2000) / 2) (25479013 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (41 / 2500) (33 / 2000) (1033343849 / 1000000000) (51677527 / 50000000)
    (3246249 / 1000000) (3247003 / 1000000) (25479013 / 1000000) (196239941 / 5000000000) (-21891 / 50) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell165 :
    ∀ u : ℝ, u ∈ Set.Icc ((33 / 2000) : ℝ) (83 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1033550539 / 1000000000) : ℝ) ≤ Real.exp (2 * (33 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (33 / 2000)) (1033550539 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((83 / 5000) : ℝ)) ≤ (1033757271 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (83 / 5000)) (1033757271 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((12747149 / 500000) : ℝ) ≤ Real.exp ((3246899 / 1000000) - (83 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3246899 / 1000000) - (83 / 5000) / 2) (12747149 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (33 / 2000) (83 / 5000) (1033550539 / 1000000000) (1033757271 / 1000000000)
    (3246899 / 1000000) (811913 / 250000) (12747149 / 500000) (98061143 / 2500000000) (-219013 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell166 :
    ∀ u : ℝ, u ∈ Set.Icc ((83 / 5000) : ℝ) (167 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((103375727 / 100000000) : ℝ) ≤ Real.exp (2 * (83 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (83 / 5000)) (103375727 / 100000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((167 / 10000) : ℝ)) ≤ (1033964043 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (167 / 10000)) (1033964043 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((398587 / 15625) : ℝ) ≤ Real.exp ((811887 / 250000) - (167 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((811887 / 250000) - (167 / 10000) / 2) (398587 / 15625) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (83 / 5000) (167 / 10000) (103375727 / 100000000) (1033964043 / 1000000000)
    (811887 / 250000) (1624151 / 500000) (398587 / 15625) (15680391 / 400000000) (-54779 / 125) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell167 :
    ∀ u : ℝ, u ∈ Set.Icc ((167 / 10000) : ℝ) (21 / 1250) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((516982021 / 500000000) : ℝ) ≤ Real.exp (2 * (167 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (167 / 10000)) (516982021 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((21 / 1250) : ℝ)) ≤ (129271357 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (21 / 1250)) (129271357 / 125000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((3190609 / 125000) : ℝ) ≤ Real.exp ((1624099 / 500000) - (21 / 1250) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1624099 / 500000) - (21 / 1250) / 2) (3190609 / 125000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (167 / 10000) (21 / 1250) (516982021 / 500000000) (129271357 / 125000000)
    (1624099 / 500000) (406119 / 125000) (3190609 / 125000) (391774737 / 10000000000) (-219219 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell168 :
    ∀ u : ℝ, u ∈ Set.Icc ((21 / 1250) : ℝ) (169 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((206834171 / 200000000) : ℝ) ≤ Real.exp (2 * (21 / 1250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (21 / 1250)) (206834171 / 200000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((169 / 10000) : ℝ)) ≤ (1034377711 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (169 / 10000)) (1034377711 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((79813 / 3125) : ℝ) ≤ Real.exp ((3248847 / 1000000) - (169 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3248847 / 1000000) - (169 / 10000) / 2) (79813 / 3125) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (21 / 1250) (169 / 10000) (206834171 / 200000000) (1034377711 / 1000000000)
    (3248847 / 1000000) (1624801 / 500000) (79813 / 3125) (195770113 / 5000000000) (-87729 / 200) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell169 :
    ∀ u : ℝ, u ∈ Set.Icc ((169 / 10000) : ℝ) (17 / 1000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((103437771 / 100000000) : ℝ) ≤ Real.exp (2 * (169 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (169 / 10000)) (103437771 / 100000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((17 / 1000) : ℝ)) ≤ (1034584607 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (17 / 1000)) (1034584607 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((12777741 / 500000) : ℝ) ≤ Real.exp ((3249497 / 1000000) - (17 / 1000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3249497 / 1000000) - (17 / 1000) / 2) (12777741 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (169 / 10000) (17 / 1000) (103437771 / 100000000) (1034584607 / 1000000000)
    (3249497 / 1000000) (812563 / 250000) (12777741 / 500000) (15652219 / 400000000) (-438851 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cellsBatch016 :
    ∀ u : ℝ, u ∈ Set.Icc ((2 / 125) : ℝ) (17 / 1000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  exact (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell160
      hpThetaCNV_secondDerivative_cell161)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell162
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell163
      hpThetaCNV_secondDerivative_cell164)))
      (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell165
      hpThetaCNV_secondDerivative_cell166)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell167
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell168
      hpThetaCNV_secondDerivative_cell169))))

#print axioms hpThetaCNV_secondDerivative_cellsBatch016
end HodgeProofHP
