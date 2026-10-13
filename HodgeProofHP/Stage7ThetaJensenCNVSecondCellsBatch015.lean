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

theorem hpThetaCNV_secondDerivative_cell150 :
    ∀ u : ℝ, u ∈ Set.Icc ((3 / 200) : ℝ) (151 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1030454533 / 1000000000) : ℝ) ≤ Real.exp (2 * (3 / 200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3 / 200)) (1030454533 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((151 / 10000) : ℝ)) ≤ (515330323 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (151 / 10000)) (515330323 / 500000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25266551 / 1000000) : ℝ) ≤ Real.exp ((809293 / 250000) - (151 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((809293 / 250000) - (151 / 10000) / 2) (25266551 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (3 / 200) (151 / 10000) (1030454533 / 1000000000) (515330323 / 500000000)
    (809293 / 250000) (809481 / 250000) (25266551 / 1000000) (24736261 / 625000000) (-434929 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell151 :
    ∀ u : ℝ, u ∈ Set.Icc ((151 / 10000) : ℝ) (19 / 1250) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((206132129 / 200000000) : ℝ) ≤ Real.exp (2 * (151 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (151 / 10000)) (206132129 / 200000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((19 / 1250) : ℝ)) ≤ (1030866799 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (19 / 1250)) (1030866799 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25281659 / 1000000) : ℝ) ≤ Real.exp ((161891 / 50000) - (19 / 1250) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((161891 / 50000) - (19 / 1250) / 2) (25281659 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (151 / 10000) (19 / 1250) (206132129 / 200000000) (1030866799 / 1000000000)
    (161891 / 50000) (809643 / 250000) (25281659 / 1000000) (395543663 / 10000000000) (-87027 / 200) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell152 :
    ∀ u : ℝ, u ∈ Set.Icc ((19 / 1250) : ℝ) (153 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((515433399 / 500000000) : ℝ) ≤ Real.exp (2 * (19 / 1250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (19 / 1250)) (515433399 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((153 / 10000) : ℝ)) ≤ (1031072993 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (153 / 10000)) (1031072993 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((3162097 / 125000) : ℝ) ≤ Real.exp ((809617 / 250000) - (153 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((809617 / 250000) - (153 / 10000) / 2) (3162097 / 125000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (19 / 1250) (153 / 10000) (515433399 / 500000000) (1031072993 / 1000000000)
    (809617 / 250000) (3239219 / 1000000) (3162097 / 125000) (98826823 / 2500000000) (-217671 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell153 :
    ∀ u : ℝ, u ∈ Set.Icc ((153 / 10000) : ℝ) (77 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((32221031 / 31250000) : ℝ) ≤ Real.exp (2 * (153 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (153 / 10000)) (32221031 / 31250000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((77 / 5000) : ℝ)) ≤ (257819807 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (77 / 5000)) (257819807 / 250000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((6327969 / 250000) : ℝ) ≤ Real.exp ((647823 / 200000) - (77 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((647823 / 200000) - (77 / 5000) / 2) (6327969 / 250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (153 / 10000) (77 / 5000) (32221031 / 31250000) (257819807 / 250000000)
    (647823 / 200000) (3239867 / 1000000) (6327969 / 250000) (98767867 / 2500000000) (-108887 / 250) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell154 :
    ∀ u : ℝ, u ∈ Set.Icc ((77 / 5000) : ℝ) (31 / 2000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1031279227 / 1000000000) : ℝ) ≤ Real.exp (2 * (77 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (77 / 5000)) (1031279227 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((31 / 2000) : ℝ)) ≤ (16116961 / 15625000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (31 / 2000)) (16116961 / 15625000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25327011 / 1000000) : ℝ) ≤ Real.exp ((3239763 / 1000000) - (31 / 2000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3239763 / 1000000) - (31 / 2000) / 2) (25327011 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (77 / 5000) (31 / 2000) (1031279227 / 1000000000) (16116961 / 15625000)
    (3239763 / 1000000) (648103 / 200000) (25327011 / 1000000) (19741769 / 500000000) (-87151 / 200) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell155 :
    ∀ u : ℝ, u ∈ Set.Icc ((31 / 2000) : ℝ) (39 / 2500) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1031485503 / 1000000000) : ℝ) ≤ Real.exp (2 * (31 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (31 / 2000)) (1031485503 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((39 / 2500) : ℝ)) ≤ (515845911 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (39 / 2500)) (515845911 / 500000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((6335539 / 250000) : ℝ) ≤ Real.exp ((3240411 / 1000000) - (39 / 2500) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3240411 / 1000000) - (39 / 2500) / 2) (6335539 / 250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (31 / 2000) (39 / 2500) (1031485503 / 1000000000) (515845911 / 500000000)
    (3240411 / 1000000) (810291 / 250000) (6335539 / 250000) (197299709 / 5000000000) (-217981 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell156 :
    ∀ u : ℝ, u ∈ Set.Icc ((39 / 2500) : ℝ) (157 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1031691821 / 1000000000) : ℝ) ≤ Real.exp (2 * (39 / 2500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (39 / 2500)) (1031691821 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((157 / 10000) : ℝ)) ≤ (1031898181 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (157 / 10000)) (1031898181 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25357309 / 1000000) : ℝ) ≤ Real.exp ((3241059 / 1000000) - (157 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3241059 / 1000000) - (157 / 10000) / 2) (25357309 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (39 / 2500) (157 / 10000) (1031691821 / 1000000000) (1031898181 / 1000000000)
    (3241059 / 1000000) (810453 / 250000) (25357309 / 1000000) (197181807 / 5000000000) (-54521 / 125) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell157 :
    ∀ u : ℝ, u ∈ Set.Icc ((157 / 10000) : ℝ) (79 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((51594909 / 50000000) : ℝ) ≤ Real.exp (2 * (157 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (157 / 10000)) (51594909 / 50000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((79 / 5000) : ℝ)) ≤ (1032104581 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (79 / 5000)) (1032104581 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((1585781 / 62500) : ℝ) ≤ Real.exp ((810427 / 250000) - (79 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((810427 / 250000) - (79 / 5000) / 2) (1585781 / 62500) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (157 / 10000) (79 / 5000) (51594909 / 50000000) (1032104581 / 1000000000)
    (810427 / 250000) (162123 / 50000) (1585781 / 62500) (394127563 / 10000000000) (-3491 / 8) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell158 :
    ∀ u : ℝ, u ∈ Set.Icc ((79 / 5000) : ℝ) (159 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((51605229 / 50000000) : ℝ) ≤ Real.exp (2 * (79 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (79 / 5000)) (51605229 / 50000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((159 / 10000) : ℝ)) ≤ (1032311023 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (159 / 10000)) (1032311023 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25387667 / 1000000) : ℝ) ≤ Real.exp ((810589 / 250000) - (159 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((810589 / 250000) - (159 / 10000) / 2) (25387667 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (79 / 5000) (159 / 10000) (51605229 / 50000000) (1032311023 / 1000000000)
    (810589 / 250000) (3243109 / 1000000) (25387667 / 1000000) (393892043 / 10000000000) (-436581 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell159 :
    ∀ u : ℝ, u ∈ Set.Icc ((159 / 10000) : ℝ) (2 / 125) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((516155511 / 500000000) : ℝ) ≤ Real.exp (2 * (159 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (159 / 10000)) (516155511 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((2 / 125) : ℝ)) ≤ (516258753 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2 / 125)) (516258753 / 500000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25402873 / 1000000) : ℝ) ≤ Real.exp ((648601 / 200000) - (2 / 125) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((648601 / 200000) - (2 / 125) / 2) (25402873 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (159 / 10000) (2 / 125) (516155511 / 500000000) (516258753 / 500000000)
    (648601 / 200000) (3243757 / 1000000) (25402873 / 1000000) (393656261 / 10000000000) (-109197 / 250) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cellsBatch015 :
    ∀ u : ℝ, u ∈ Set.Icc ((3 / 200) : ℝ) (2 / 125) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  exact (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell150
      hpThetaCNV_secondDerivative_cell151)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell152
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell153
      hpThetaCNV_secondDerivative_cell154)))
      (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell155
      hpThetaCNV_secondDerivative_cell156)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell157
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell158
      hpThetaCNV_secondDerivative_cell159))))

#print axioms hpThetaCNV_secondDerivative_cellsBatch015
end HodgeProofHP
