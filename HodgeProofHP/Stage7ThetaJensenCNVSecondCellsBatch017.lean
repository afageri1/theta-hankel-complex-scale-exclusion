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

theorem hpThetaCNV_secondDerivative_cell170 :
    ∀ u : ℝ, u ∈ Set.Icc ((17 / 1000) : ℝ) (171 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((517292303 / 500000000) : ℝ) ≤ Real.exp (2 * (17 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (17 / 1000)) (517292303 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((171 / 10000) : ℝ)) ≤ (206958309 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (171 / 10000)) (206958309 / 200000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((12785407 / 500000) : ℝ) ≤ Real.exp ((3250147 / 1000000) - (171 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3250147 / 1000000) - (171 / 10000) / 2) (12785407 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (17 / 1000) (171 / 10000) (517292303 / 500000000) (206958309 / 200000000)
    (3250147 / 1000000) (1625451 / 500000) (12785407 / 500000) (97767713 / 2500000000) (-439057 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell171 :
    ∀ u : ℝ, u ∈ Set.Icc ((171 / 10000) : ℝ) (43 / 2500) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((129348943 / 125000000) : ℝ) ≤ Real.exp (2 * (171 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (171 / 10000)) (129348943 / 125000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((43 / 2500) : ℝ)) ≤ (258749631 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (43 / 2500)) (258749631 / 250000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((5117231 / 200000) : ℝ) ≤ Real.exp ((3250797 / 1000000) - (43 / 2500) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3250797 / 1000000) - (43 / 2500) / 2) (5117231 / 200000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (171 / 10000) (43 / 2500) (129348943 / 125000000) (258749631 / 250000000)
    (3250797 / 1000000) (101611 / 31250) (5117231 / 200000) (390836373 / 10000000000) (-439263 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell172 :
    ∀ u : ℝ, u ∈ Set.Icc ((43 / 2500) : ℝ) (173 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1034998523 / 1000000000) : ℝ) ≤ Real.exp (2 * (43 / 2500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (43 / 2500)) (1034998523 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((173 / 10000) : ℝ)) ≤ (129400693 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (173 / 10000)) (129400693 / 125000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((5120301 / 200000) : ℝ) ≤ Real.exp ((3251447 / 1000000) - (173 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3251447 / 1000000) - (173 / 10000) / 2) (5120301 / 200000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (43 / 2500) (173 / 10000) (1034998523 / 1000000000) (129400693 / 125000000)
    (3251447 / 1000000) (1626101 / 500000) (5120301 / 200000) (390602037 / 10000000000) (-439469 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell173 :
    ∀ u : ℝ, u ∈ Set.Icc ((173 / 10000) : ℝ) (87 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1035205543 / 1000000000) : ℝ) ≤ Real.exp (2 * (173 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (173 / 10000)) (1035205543 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((87 / 5000) : ℝ)) ≤ (517706303 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (87 / 5000)) (517706303 / 500000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((2561689 / 100000) : ℝ) ≤ Real.exp ((1626049 / 500000) - (87 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1626049 / 500000) - (87 / 5000) / 2) (2561689 / 100000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (173 / 10000) (87 / 5000) (1035205543 / 1000000000) (517706303 / 500000000)
    (1626049 / 500000) (3252853 / 1000000) (2561689 / 100000) (390367449 / 10000000000) (-17587 / 40) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell174 :
    ∀ u : ℝ, u ∈ Set.Icc ((87 / 5000) : ℝ) (7 / 400) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((207082521 / 200000000) : ℝ) ≤ Real.exp (2 * (87 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (87 / 5000)) (207082521 / 200000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((7 / 400) : ℝ)) ≤ (1035619709 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (7 / 400)) (1035619709 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((12816129 / 500000) : ℝ) ≤ Real.exp ((813187 / 250000) - (7 / 400) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((813187 / 250000) - (7 / 400) / 2) (12816129 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (87 / 5000) (7 / 400) (207082521 / 200000000) (1035619709 / 1000000000)
    (813187 / 250000) (3253503 / 1000000) (12816129 / 500000) (195066701 / 5000000000) (-439881 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell175 :
    ∀ u : ℝ, u ∈ Set.Icc ((7 / 400) : ℝ) (11 / 625) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((258904927 / 250000000) : ℝ) ≤ Real.exp (2 * (7 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (7 / 400)) (258904927 / 250000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((11 / 625) : ℝ)) ≤ (517913427 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (11 / 625)) (517913427 / 500000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25647661 / 1000000) : ℝ) ≤ Real.exp ((3253399 / 1000000) - (11 / 625) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3253399 / 1000000) - (11 / 625) / 2) (25647661 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (7 / 400) (11 / 625) (258904927 / 250000000) (517913427 / 500000000)
    (3253399 / 1000000) (1627077 / 500000) (25647661 / 1000000) (389899103 / 10000000000) (-440087 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell176 :
    ∀ u : ℝ, u ∈ Set.Icc ((11 / 625) : ℝ) (177 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1035826853 / 1000000000) : ℝ) ≤ Real.exp (2 * (11 / 625)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (11 / 625)) (1035826853 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((177 / 10000) : ℝ)) ≤ (25900851 / 25000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (177 / 10000)) (25900851 / 25000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((12831537 / 500000) : ℝ) ≤ Real.exp ((65081 / 20000) - (177 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((65081 / 20000) - (177 / 10000) / 2) (12831537 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (11 / 625) (177 / 10000) (1035826853 / 1000000000) (25900851 / 25000000)
    (65081 / 20000) (650961 / 200000) (12831537 / 500000) (389664933 / 10000000000) (-440293 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell177 :
    ∀ u : ℝ, u ∈ Set.Icc ((177 / 10000) : ℝ) (89 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1036034039 / 1000000000) : ℝ) ≤ Real.exp (2 * (177 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (177 / 10000)) (1036034039 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((89 / 5000) : ℝ)) ≤ (259060317 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (89 / 5000)) (259060317 / 250000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((2567847 / 100000) : ℝ) ≤ Real.exp ((32547 / 10000) - (89 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((32547 / 10000) - (89 / 5000) / 2) (2567847 / 100000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (177 / 10000) (89 / 5000) (1036034039 / 1000000000) (259060317 / 250000000)
    (32547 / 10000) (101733 / 31250) (2567847 / 100000) (194715651 / 5000000000) (-440499 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell178 :
    ∀ u : ℝ, u ∈ Set.Icc ((89 / 5000) : ℝ) (179 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1036241267 / 1000000000) : ℝ) ≤ Real.exp (2 * (89 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (89 / 5000)) (1036241267 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((179 / 10000) : ℝ)) ≤ (1036448537 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (179 / 10000)) (1036448537 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25693901 / 1000000) : ℝ) ≤ Real.exp ((3255351 / 1000000) - (179 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3255351 / 1000000) - (179 / 10000) / 2) (25693901 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (89 / 5000) (179 / 10000) (1036241267 / 1000000000) (1036448537 / 1000000000)
    (3255351 / 1000000) (3256107 / 1000000) (25693901 / 1000000) (389197421 / 10000000000) (-55088 / 125) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell179 :
    ∀ u : ℝ, u ∈ Set.Icc ((179 / 10000) : ℝ) (9 / 500) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((129556067 / 125000000) : ℝ) ≤ Real.exp (2 * (179 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (179 / 10000)) (129556067 / 125000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((9 / 500) : ℝ)) ≤ (1036655847 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9 / 500)) (1036655847 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25709367 / 1000000) : ℝ) ≤ Real.exp ((3256003 / 1000000) - (9 / 500) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3256003 / 1000000) - (9 / 500) / 2) (25709367 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (179 / 10000) (9 / 500) (129556067 / 125000000) (1036655847 / 1000000000)
    (3256003 / 1000000) (3256759 / 1000000) (25709367 / 1000000) (97240823 / 2500000000) (-44091 / 100) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cellsBatch017 :
    ∀ u : ℝ, u ∈ Set.Icc ((17 / 1000) : ℝ) (9 / 500) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  exact (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell170
      hpThetaCNV_secondDerivative_cell171)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell172
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell173
      hpThetaCNV_secondDerivative_cell174)))
      (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell175
      hpThetaCNV_secondDerivative_cell176)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell177
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell178
      hpThetaCNV_secondDerivative_cell179))))

#print axioms hpThetaCNV_secondDerivative_cellsBatch017
end HodgeProofHP
