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

theorem hpThetaCNV_secondDerivative_cell060 :
    ∀ u : ℝ, u ∈ Set.Icc ((3 / 500) : ℝ) (61 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((31627259 / 31250000) : ℝ) ≤ Real.exp (2 * (3 / 500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3 / 500)) (31627259 / 31250000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((61 / 10000) : ℝ)) ≤ (253068681 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (61 / 10000)) (253068681 / 250000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((23956847 / 1000000) : ℝ) ≤ Real.exp ((127177 / 40000) - (61 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((127177 / 40000) - (61 / 10000) / 2) (23956847 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (3 / 500) (61 / 10000) (31627259 / 31250000) (253068681 / 250000000)
    (127177 / 40000) (3180163 / 1000000) (23956847 / 1000000) (417417201 / 10000000000) (-52029 / 125) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell061 :
    ∀ u : ℝ, u ∈ Set.Icc ((61 / 10000) : ℝ) (31 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1012274723 / 1000000000) : ℝ) ≤ Real.exp (2 * (61 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (61 / 10000)) (1012274723 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((31 / 5000) : ℝ)) ≤ (1012477199 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (31 / 5000)) (1012477199 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((4794177 / 200000) : ℝ) ≤ Real.exp ((3180061 / 1000000) - (31 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3180061 / 1000000) - (31 / 5000) / 2) (4794177 / 200000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (61 / 10000) (31 / 5000) (1012274723 / 1000000000) (1012477199 / 1000000000)
    (3180061 / 1000000) (3180799 / 1000000) (4794177 / 200000) (1668691 / 40000000) (-416441 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell062 :
    ∀ u : ℝ, u ∈ Set.Icc ((31 / 5000) : ℝ) (63 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((506238599 / 500000000) : ℝ) ≤ Real.exp (2 * (31 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (31 / 5000)) (506238599 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((63 / 10000) : ℝ)) ≤ (202535943 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (63 / 10000)) (202535943 / 200000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((23984931 / 1000000) : ℝ) ≤ Real.exp ((3180697 / 1000000) - (63 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3180697 / 1000000) - (63 / 10000) / 2) (23984931 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (31 / 5000) (63 / 10000) (506238599 / 500000000) (202535943 / 200000000)
    (3180697 / 1000000) (636287 / 200000) (23984931 / 1000000) (208464223 / 5000000000) (-416649 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell063 :
    ∀ u : ℝ, u ∈ Set.Icc ((63 / 10000) : ℝ) (4 / 625) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((506339857 / 500000000) : ℝ) ≤ Real.exp (2 * (63 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (63 / 10000)) (506339857 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((4 / 625) : ℝ)) ≤ (1012882271 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4 / 625)) (1012882271 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((4799797 / 200000) : ℝ) ≤ Real.exp ((3181333 / 1000000) - (4 / 625) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3181333 / 1000000) - (4 / 625) / 2) (4799797 / 200000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (63 / 10000) (4 / 625) (506339857 / 500000000) (1012882271 / 1000000000)
    (3181333 / 1000000) (3182071 / 1000000) (4799797 / 200000) (416684289 / 10000000000) (-416857 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell064 :
    ∀ u : ℝ, u ∈ Set.Icc ((4 / 625) : ℝ) (13 / 2000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((101288227 / 100000000) : ℝ) ≤ Real.exp (2 * (4 / 625)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4 / 625)) (101288227 / 100000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((13 / 2000) : ℝ)) ≤ (253271217 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (13 / 2000)) (253271217 / 250000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((3001631 / 125000) : ℝ) ≤ Real.exp ((3181969 / 1000000) - (13 / 2000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3181969 / 1000000) - (13 / 2000) / 2) (3001631 / 125000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (4 / 625) (13 / 2000) (101288227 / 100000000) (253271217 / 250000000)
    (3181969 / 1000000) (795677 / 250000) (3001631 / 125000) (208220131 / 5000000000) (-208533 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell065 :
    ∀ u : ℝ, u ∈ Set.Icc ((13 / 2000) : ℝ) (33 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1013084867 / 1000000000) : ℝ) ≤ Real.exp (2 * (13 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (13 / 2000)) (1013084867 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((33 / 5000) : ℝ)) ≤ (202657501 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (33 / 5000)) (202657501 / 200000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((24027143 / 1000000) : ℝ) ≤ Real.exp ((1591303 / 500000) - (33 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1591303 / 500000) - (33 / 5000) / 2) (24027143 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (13 / 2000) (33 / 5000) (1013084867 / 1000000000) (202657501 / 200000000)
    (1591303 / 500000) (636669 / 200000) (24027143 / 1000000) (416195967 / 10000000000) (-16691 / 40) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell066 :
    ∀ u : ℝ, u ∈ Set.Icc ((33 / 5000) : ℝ) (67 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((63330469 / 62500000) : ℝ) ≤ Real.exp (2 * (33 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (33 / 5000)) (63330469 / 62500000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((67 / 10000) : ℝ)) ≤ (1013490183 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (67 / 10000)) (1013490183 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((12020611 / 500000) : ℝ) ≤ Real.exp ((1591621 / 500000) - (67 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1591621 / 500000) - (67 / 10000) / 2) (12020611 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (33 / 5000) (67 / 10000) (63330469 / 62500000) (1013490183 / 1000000000)
    (1591621 / 500000) (3183981 / 1000000) (12020611 / 500000) (83190447 / 2000000000) (-417483 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell067 :
    ∀ u : ℝ, u ∈ Set.Icc ((67 / 10000) : ℝ) (17 / 2500) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((506745091 / 500000000) : ℝ) ≤ Real.exp (2 * (67 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (67 / 10000)) (506745091 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((17 / 2500) : ℝ)) ≤ (1013692901 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (17 / 2500)) (1013692901 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((24055333 / 1000000) : ℝ) ≤ Real.exp ((3183879 / 1000000) - (17 / 2500) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3183879 / 1000000) - (17 / 2500) / 2) (24055333 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (67 / 10000) (17 / 2500) (506745091 / 500000000) (1013692901 / 1000000000)
    (3183879 / 1000000) (1592309 / 500000) (24055333 / 1000000) (83141647 / 2000000000) (-417691 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell068 :
    ∀ u : ℝ, u ∈ Set.Icc ((17 / 2500) : ℝ) (69 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((10136929 / 10000000) : ℝ) ≤ Real.exp (2 * (17 / 2500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (17 / 2500)) (10136929 / 10000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((69 / 10000) : ℝ)) ≤ (50694783 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (69 / 10000)) (50694783 / 50000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((24069453 / 1000000) : ℝ) ≤ Real.exp ((796129 / 250000) - (69 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((796129 / 250000) - (69 / 10000) / 2) (24069453 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (17 / 2500) (69 / 10000) (10136929 / 10000000) (50694783 / 50000000)
    (796129 / 250000) (637051 / 200000) (24069453 / 1000000) (83092873 / 2000000000) (-4179 / 10) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell069 :
    ∀ u : ℝ, u ∈ Set.Icc ((69 / 10000) : ℝ) (7 / 1000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1013895659 / 1000000000) : ℝ) ≤ Real.exp (2 * (69 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (69 / 10000)) (1013895659 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((7 / 1000) : ℝ)) ≤ (1014098459 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (7 / 1000)) (1014098459 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((24083581 / 1000000) : ℝ) ≤ Real.exp ((3185153 / 1000000) - (7 / 1000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3185153 / 1000000) - (7 / 1000) / 2) (24083581 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (69 / 10000) (7 / 1000) (1013895659 / 1000000000) (1014098459 / 1000000000)
    (3185153 / 1000000) (796473 / 250000) (24083581 / 1000000) (103805161 / 2500000000) (-104527 / 250) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cellsBatch006 :
    ∀ u : ℝ, u ∈ Set.Icc ((3 / 500) : ℝ) (7 / 1000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  exact (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell060
      hpThetaCNV_secondDerivative_cell061)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell062
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell063
      hpThetaCNV_secondDerivative_cell064)))
      (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell065
      hpThetaCNV_secondDerivative_cell066)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell067
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell068
      hpThetaCNV_secondDerivative_cell069))))

#print axioms hpThetaCNV_secondDerivative_cellsBatch006
end HodgeProofHP
