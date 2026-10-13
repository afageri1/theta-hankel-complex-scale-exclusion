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

theorem hpThetaCNV_secondDerivative_cell130 :
    ∀ u : ℝ, u ∈ Set.Icc ((13 / 1000) : ℝ) (131 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((256585237 / 250000000) : ℝ) ≤ Real.exp (2 * (13 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (13 / 1000)) (256585237 / 250000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((131 / 10000) : ℝ)) ≤ (513273119 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (131 / 10000)) (513273119 / 500000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((6241807 / 250000) : ℝ) ≤ Real.exp ((12897 / 4000) - (131 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((12897 / 4000) - (131 / 10000) / 2) (6241807 / 250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (13 / 1000) (131 / 10000) (256585237 / 250000000) (513273119 / 500000000)
    (12897 / 4000) (1612499 / 500000) (6241807 / 250000) (400525041 / 10000000000) (-430789 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell131 :
    ∀ u : ℝ, u ∈ Set.Icc ((131 / 10000) : ℝ) (33 / 2500) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1026546237 / 1000000000) : ℝ) ≤ Real.exp (2 * (131 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (131 / 10000)) (1026546237 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((33 / 2500) : ℝ)) ≤ (1026751567 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (33 / 2500)) (1026751567 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((12491041 / 500000) : ℝ) ≤ Real.exp ((644979 / 200000) - (33 / 2500) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((644979 / 200000) - (33 / 2500) / 2) (12491041 / 500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (131 / 10000) (33 / 2500) (1026546237 / 1000000000) (1026751567 / 1000000000)
    (644979 / 200000) (3225643 / 1000000) (12491041 / 500000) (200143447 / 5000000000) (-107749 / 250) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell132 :
    ∀ u : ℝ, u ∈ Set.Icc ((33 / 2500) : ℝ) (133 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((513375783 / 500000000) : ℝ) ≤ Real.exp (2 * (33 / 2500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (33 / 2500)) (513375783 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((133 / 10000) : ℝ)) ≤ (513478469 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (133 / 10000)) (513478469 / 500000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((4999389 / 200000) : ℝ) ≤ Real.exp ((161277 / 50000) - (133 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((161277 / 50000) - (133 / 10000) / 2) (4999389 / 200000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (33 / 2500) (133 / 10000) (513375783 / 500000000) (513478469 / 500000000)
    (161277 / 50000) (201643 / 62500) (4999389 / 200000) (200024443 / 5000000000) (-431203 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell133 :
    ∀ u : ℝ, u ∈ Set.Icc ((133 / 10000) : ℝ) (67 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1026956937 / 1000000000) : ℝ) ≤ Real.exp (2 * (133 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (133 / 10000)) (1026956937 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((67 / 5000) : ℝ)) ≤ (20543247 / 20000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (67 / 5000)) (20543247 / 20000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25011817 / 1000000) : ℝ) ≤ Real.exp ((645237 / 200000) - (67 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((645237 / 200000) - (67 / 5000) / 2) (25011817 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (133 / 10000) (67 / 5000) (1026956937 / 1000000000) (20543247 / 20000000)
    (645237 / 200000) (1613467 / 500000) (25011817 / 1000000) (199905509 / 5000000000) (-431411 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell134 :
    ∀ u : ℝ, u ∈ Set.Icc ((67 / 5000) : ℝ) (27 / 2000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((1027162349 / 1000000000) : ℝ) ≤ Real.exp (2 * (67 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (67 / 5000)) (1027162349 / 1000000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((27 / 2000) : ℝ)) ≤ (1027367803 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (27 / 2000)) (1027367803 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25026697 / 1000000) : ℝ) ≤ Real.exp ((322683 / 100000) - (27 / 2000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((322683 / 100000) - (27 / 2000) / 2) (25026697 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (67 / 5000) (27 / 2000) (1027162349 / 1000000000) (1027367803 / 1000000000)
    (322683 / 100000) (3227579 / 1000000) (25026697 / 1000000) (49946663 / 1250000000) (-215809 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell135 :
    ∀ u : ℝ, u ∈ Set.Icc ((27 / 2000) : ℝ) (17 / 1250) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((513683901 / 500000000) : ℝ) ≤ Real.exp (2 * (27 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (27 / 2000)) (513683901 / 500000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((17 / 1250) : ℝ)) ≤ (1027573297 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (17 / 1250)) (1027573297 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25041587 / 1000000) : ℝ) ≤ Real.exp ((129099 / 40000) - (17 / 1250) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((129099 / 40000) - (17 / 1250) / 2) (25041587 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (27 / 2000) (17 / 1250) (513683901 / 500000000) (1027573297 / 1000000000)
    (129099 / 40000) (129129 / 40000) (25041587 / 1000000) (199667857 / 5000000000) (-17273 / 40) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell136 :
    ∀ u : ℝ, u ∈ Set.Icc ((17 / 1250) : ℝ) (137 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((64223331 / 62500000) : ℝ) ≤ Real.exp (2 * (17 / 1250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (17 / 1250)) (64223331 / 62500000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((137 / 10000) : ℝ)) ≤ (1027778833 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (137 / 10000)) (1027778833 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((2505651 / 100000) : ℝ) ≤ Real.exp ((3228121 / 1000000) - (137 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3228121 / 1000000) - (137 / 10000) / 2) (2505651 / 100000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (17 / 1250) (137 / 10000) (64223331 / 62500000) (1027778833 / 1000000000)
    (3228121 / 1000000) (322887 / 100000) (2505651 / 100000) (9977447 / 250000000) (-54004 / 125) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell137 :
    ∀ u : ℝ, u ∈ Set.Icc ((137 / 10000) : ℝ) (69 / 5000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((64236177 / 62500000) : ℝ) ≤ Real.exp (2 * (137 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (137 / 10000)) (64236177 / 62500000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((69 / 5000) : ℝ)) ≤ (1027984409 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (69 / 5000)) (1027984409 / 1000000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25071443 / 1000000) : ℝ) ≤ Real.exp ((3228767 / 1000000) - (69 / 5000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3228767 / 1000000) - (69 / 5000) / 2) (25071443 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (137 / 10000) (69 / 5000) (64236177 / 62500000) (1027984409 / 1000000000)
    (3228767 / 1000000) (807379 / 250000) (25071443 / 1000000) (39886017 / 1000000000) (-432239 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell138 :
    ∀ u : ℝ, u ∈ Set.Icc ((69 / 5000) : ℝ) (139 / 10000) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((128498051 / 125000000) : ℝ) ≤ Real.exp (2 * (69 / 5000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (69 / 5000)) (128498051 / 125000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((139 / 10000) : ℝ)) ≤ (514095013 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (139 / 10000)) (514095013 / 500000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((1567899 / 62500) : ℝ) ≤ Real.exp ((3229413 / 1000000) - (139 / 10000) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((3229413 / 1000000) - (139 / 10000) / 2) (1567899 / 62500) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (69 / 5000) (139 / 10000) (128498051 / 125000000) (514095013 / 500000000)
    (3229413 / 1000000) (1615081 / 500000) (1567899 / 62500) (49827827 / 1250000000) (-216223 / 500) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cell139 :
    ∀ u : ℝ, u ∈ Set.Icc ((139 / 10000) : ℝ) (7 / 500) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  have hlexp : ((41127601 / 40000000) : ℝ) ≤ Real.exp (2 * (139 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (139 / 10000)) (41127601 / 40000000) 6
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hrexp : Real.exp (2 * ((7 / 500) : ℝ)) ≤ (205679137 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (7 / 500)) (205679137 / 200000000) 6
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvexp : ((25101309 / 1000000) : ℝ) ≤ Real.exp ((1615029 / 500000) - (7 / 500) / 2) := by
    exact hpThetaTrace_exp_lower_of_taylor ((1615029 / 500000) - (7 / 500) / 2) (25101309 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := hpThetaCNV_secondDerivative_rational_interval_certificate
    (139 / 10000) (7 / 500) (41127601 / 40000000) (205679137 / 200000000)
    (1615029 / 500000) (403851 / 125000) (25101309 / 1000000) (398385599 / 10000000000) (-432653 / 1000) (-35)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hlexp hrexp (by norm_num) (by norm_num) hvexp (by norm_num)
    (by norm_num [hpThetaCNVSecondFactor]) (by norm_num)
  intro u hu
  exact h u hu.1 hu.2

theorem hpThetaCNV_secondDerivative_cellsBatch013 :
    ∀ u : ℝ, u ∈ Set.Icc ((13 / 1000) : ℝ) (7 / 500) →
      (-35 : ℝ) ≤ hpThetaGaussianKernelSecondDerivativeTerm Real.pi u := by
  exact (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell130
      hpThetaCNV_secondDerivative_cell131)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell132
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell133
      hpThetaCNV_secondDerivative_cell134)))
      (hpThetaCNV_interval_lower_glue (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell135
      hpThetaCNV_secondDerivative_cell136)
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell137
      (hpThetaCNV_interval_lower_glue hpThetaCNV_secondDerivative_cell138
      hpThetaCNV_secondDerivative_cell139))))

#print axioms hpThetaCNV_secondDerivative_cellsBatch013
end HodgeProofHP
