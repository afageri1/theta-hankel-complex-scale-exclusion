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

theorem hpThetaCNV_secondDerivative_cell110 :
    ∀ u : ℝ, u ∈ Set.Icc ((11 / 1000) : ℝ) (111 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((127780473 / 125000000) : ℝ) ≤ Real.exp (2 * (11 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (11 / 1000)) (127780473 / 125000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((111 / 10000) : ℝ)) ≤ (511224127 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (111 / 10000)) (511224127 / 500000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((616817 / 25000) : ℝ) ≤ Real.exp ((1605689 / 500000) - (111 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1605689 / 500000) - (111 / 10000) / 2) (616817 / 25000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (11 / 1000) (111 / 10000) (127780473 / 125000000) (511224127 / 500000000)
    (1605689 / 500000) (803031 / 250000) (616817 / 25000) (405306599 / 10000000000) (-10666 / 25) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell111 :
    ∀ u : ℝ, u ∈ Set.Icc ((111 / 10000) : ℝ) (7 / 625) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1022448253 / 1000000000) : ℝ) ≤ Real.exp (2 * (111 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (111 / 10000)) (1022448253 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((7 / 625) : ℝ)) ≤ (255663191 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (7 / 625)) (255663191 / 250000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((2468731 / 100000) : ℝ) ≤ Real.exp ((3212021 / 1000000) - (7 / 625) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3212021 / 1000000) - (7 / 625) / 2) (2468731 / 100000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (111 / 10000) (7 / 625) (1022448253 / 1000000000) (255663191 / 250000000)
    (3212021 / 1000000) (1606383 / 500000) (2468731 / 100000) (405066409 / 10000000000) (-426847 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell112 :
    ∀ u : ℝ, u ∈ Set.Icc ((7 / 625) : ℝ) (113 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1022652763 / 1000000000) : ℝ) ≤ Real.exp (2 * (7 / 625)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (7 / 625)) (1022652763 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((113 / 10000) : ℝ)) ≤ (204571463 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (113 / 10000)) (204571463 / 200000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((6175481 / 250000) : ℝ) ≤ Real.exp ((3212663 / 1000000) - (113 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3212663 / 1000000) - (113 / 10000) / 2) (6175481 / 250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (7 / 625) (113 / 10000) (1022652763 / 1000000000) (204571463 / 200000000)
    (3212663 / 1000000) (3213409 / 1000000) (6175481 / 250000) (202413383 / 5000000000) (-85411 / 200) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell113 :
    ∀ u : ℝ, u ∈ Set.Icc ((113 / 10000) : ℝ) (57 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((511428657 / 500000000) : ℝ) ≤ Real.exp (2 * (113 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (113 / 10000)) (511428657 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((57 / 5000) : ℝ)) ≤ (1023061907 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (57 / 5000)) (1023061907 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((24716571 / 1000000) : ℝ) ≤ Real.exp ((1606653 / 500000) - (57 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1606653 / 500000) - (57 / 5000) / 2) (24716571 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (113 / 10000) (57 / 5000) (511428657 / 500000000) (1023061907 / 1000000000)
    (1606653 / 500000) (803513 / 250000) (24716571 / 1000000) (404586867 / 10000000000) (-427263 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell114 :
    ∀ u : ℝ, u ∈ Set.Icc ((57 / 5000) : ℝ) (23 / 2000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((511530953 / 500000000) : ℝ) ≤ Real.exp (2 * (57 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (57 / 5000)) (511530953 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((23 / 2000) : ℝ)) ≤ (51163327 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (23 / 2000)) (51163327 / 50000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((12365601 / 500000) : ℝ) ≤ Real.exp ((803487 / 250000) - (23 / 2000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((803487 / 250000) - (23 / 2000) / 2) (12365601 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (57 / 5000) (23 / 2000) (511530953 / 500000000) (51163327 / 50000000)
    (803487 / 250000) (642939 / 200000) (12365601 / 500000) (404347513 / 10000000000) (-42747 / 100) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell115 :
    ∀ u : ℝ, u ∈ Set.Icc ((23 / 2000) : ℝ) (29 / 2500) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1023266539 / 1000000000) : ℝ) ≤ Real.exp (2 * (23 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (23 / 2000)) (1023266539 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((29 / 2500) : ℝ)) ≤ (511735607 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (29 / 2500)) (511735607 / 500000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((12372933 / 500000) : ℝ) ≤ Real.exp ((3214591 / 1000000) - (29 / 2500) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3214591 / 1000000) - (29 / 2500) / 2) (12372933 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (23 / 2000) (29 / 2500) (1023266539 / 1000000000) (511735607 / 500000000)
    (3214591 / 1000000) (1607669 / 500000) (12372933 / 500000) (404107903 / 10000000000) (-213839 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell116 :
    ∀ u : ℝ, u ∈ Set.Icc ((29 / 2500) : ℝ) (117 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1023471213 / 1000000000) : ℝ) ≤ Real.exp (2 * (29 / 2500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (29 / 2500)) (1023471213 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((117 / 10000) : ℝ)) ≤ (1023675929 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (117 / 10000)) (1023675929 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((24760539 / 1000000) : ℝ) ≤ Real.exp ((1607617 / 500000) - (117 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1607617 / 500000) - (117 / 10000) / 2) (24760539 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (29 / 2500) (117 / 10000) (1023471213 / 1000000000) (1023675929 / 1000000000)
    (1607617 / 500000) (3215981 / 1000000) (24760539 / 1000000) (40386843 / 1000000000) (-213943 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell117 :
    ∀ u : ℝ, u ∈ Set.Icc ((117 / 10000) : ℝ) (59 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((127959491 / 125000000) : ℝ) ≤ Real.exp (2 * (117 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (117 / 10000)) (127959491 / 125000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((59 / 5000) : ℝ)) ≤ (255970171 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (59 / 5000)) (255970171 / 250000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((24775221 / 1000000) : ℝ) ≤ Real.exp ((3215877 / 1000000) - (59 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3215877 / 1000000) - (59 / 5000) / 2) (24775221 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (117 / 10000) (59 / 5000) (127959491 / 125000000) (255970171 / 250000000)
    (3215877 / 1000000) (201039 / 62500) (24775221 / 1000000) (201814547 / 5000000000) (-428093 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell118 :
    ∀ u : ℝ, u ∈ Set.Icc ((59 / 5000) : ℝ) (119 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1023880683 / 1000000000) : ℝ) ≤ Real.exp (2 * (59 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (59 / 5000)) (1023880683 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((119 / 10000) : ℝ)) ≤ (1024085481 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (119 / 10000)) (1024085481 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((1549371 / 62500) : ℝ) ≤ Real.exp ((3216521 / 1000000) - (119 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3216521 / 1000000) - (119 / 10000) / 2) (1549371 / 62500) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (59 / 5000) (119 / 10000) (1023880683 / 1000000000) (1024085481 / 1000000000)
    (3216521 / 1000000) (3217267 / 1000000) (1549371 / 62500) (80677901 / 2000000000) (-4283 / 10) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell119 :
    ∀ u : ℝ, u ∈ Set.Icc ((119 / 10000) : ℝ) (3 / 250) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((25602137 / 25000000) : ℝ) ≤ Real.exp (2 * (119 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (119 / 10000)) (25602137 / 25000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((3 / 250) : ℝ)) ≤ (512145159 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3 / 250)) (512145159 / 500000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((6201159 / 250000) : ℝ) ≤ Real.exp ((804291 / 250000) - (3 / 250) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((804291 / 250000) - (3 / 250) / 2) (6201159 / 250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (119 / 10000) (3 / 250) (25602137 / 25000000) (512145159 / 500000000)
    (804291 / 250000) (3217911 / 1000000) (6201159 / 250000) (100787611 / 2500000000) (-107127 / 250) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cellsBatch011 :
    ∀ u : ℝ, u ∈ Set.Icc ((11 / 1000) : ℝ) (3 / 250) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  exact (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell110
      hpThetaCNV_secondDerivative_cell111)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell112
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell113
      hpThetaCNV_secondDerivative_cell114)))
      (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell115
      hpThetaCNV_secondDerivative_cell116)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell117
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell118
      hpThetaCNV_secondDerivative_cell119))))

#print axioms hpThetaCNV_secondDerivative_cellsBatch011
end HodgeProofHP
