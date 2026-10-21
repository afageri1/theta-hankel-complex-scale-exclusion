/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0880 :
    ∀ t ∈ Set.Icc ((3499 / 64000) : ℝ) (3507 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((278886438323 / 250000000000) : ℝ) ≤ Real.exp (2 * (3499 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3499 / 64000)) (278886438323 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3507 / 64000) : ℝ)) ≤ (278956168649 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3507 / 64000)) (278956168649 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((964604961 / 500000000) : ℝ) ≤ Real.exp (3 * (1752294807 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1752294807 / 500000000) / 16) (964604961 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3505466987 / 1000000000) : ℝ) / 16) ≤ (1929527319 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3505466987 / 1000000000) / 16) (1929527319 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3499 / 64000) : ℝ) (3507 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1752294807 / 500000000) (3505466987 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3499 / 64000) (3507 / 64000) (278886438323 / 250000000000) (278956168649 / 250000000000) (1752294807 / 500000000) (3505466987 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3499 / 64000) (3507 / 64000) (1752294807 / 500000000) (3505466987 / 1000000000) (6772127 / 250000000000) (27159903 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1752294807 / 500000000) (3505466987 / 1000000000) (964604961 / 500000000) (1929527319 / 1000000000) (6772127 / 250000000000) (27159903 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0881 :
    ∀ t ∈ Set.Icc ((3507 / 64000) : ℝ) (3523 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((223164934919 / 200000000000) : ℝ) ≤ Real.exp (2 * (3507 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3507 / 64000)) (223164934919 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3523 / 64000) : ℝ)) ≤ (558191363217 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3523 / 64000)) (558191363217 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((964763457 / 500000000) : ℝ) ≤ Real.exp (3 * (3505465871 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3505465871 / 1000000000) / 16) (964763457 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3507220159 / 1000000000) : ℝ) / 16) ≤ (1930161697 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3507220159 / 1000000000) / 16) (1930161697 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3507 / 64000) : ℝ) (3523 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3505465871 / 1000000000) (3507220159 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3507 / 64000) (3523 / 64000) (223164934919 / 200000000000) (558191363217 / 500000000000) (3505465871 / 1000000000) (3507220159 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3507 / 64000) (3523 / 64000) (3505465871 / 1000000000) (3507220159 / 1000000000) (26946409 / 1000000000000) (135443 / 5000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3505465871 / 1000000000) (3507220159 / 1000000000) (964763457 / 500000000) (1930161697 / 1000000000) (26946409 / 1000000000000) (135443 / 5000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0882 :
    ∀ t ∈ Set.Icc ((3523 / 64000) : ℝ) (3539 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1116382726433 / 1000000000000) : ℝ) ≤ Real.exp (2 * (3523 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3523 / 64000)) (1116382726433 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3539 / 64000) : ℝ)) ≤ (139617632171 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3539 / 64000)) (139617632171 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1930161291 / 1000000000) : ℝ) ≤ Real.exp (3 * (1753609521 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1753609521 / 500000000) / 16) (1930161291 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((27413861 / 7812500) : ℝ) / 16) ≤ (1930796601 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (27413861 / 7812500) / 16) (1930796601 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3523 / 64000) : ℝ) (3539 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1753609521 / 500000000) (27413861 / 7812500) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3523 / 64000) (3539 / 64000) (1116382726433 / 1000000000000) (139617632171 / 125000000000) (1753609521 / 500000000) (27413861 / 7812500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3523 / 64000) (3539 / 64000) (1753609521 / 500000000) (27413861 / 7812500) (13402493 / 500000000000) (26946501 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1753609521 / 500000000) (27413861 / 7812500) (1930161291 / 1000000000) (1930796601 / 1000000000) (13402493 / 500000000000) (26946501 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0883 :
    ∀ t ∈ Set.Icc ((3539 / 64000) : ℝ) (711 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1116941057367 / 1000000000000) : ℝ) ≤ Real.exp (2 * (3539 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3539 / 64000)) (1116941057367 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((711 / 12800) : ℝ)) ≤ (558749833769 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (711 / 12800)) (558749833769 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((386159239 / 200000000) : ℝ) ≤ Real.exp (3 * (350897309 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (350897309 / 100000000) / 16) (386159239 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1755364567 / 500000000) : ℝ) / 16) ≤ (1931432031 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1755364567 / 500000000) / 16) (1931432031 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3539 / 64000) : ℝ) (711 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (350897309 / 100000000) (1755364567 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3539 / 64000) (711 / 12800) (1116941057367 / 1000000000000) (558749833769 / 500000000000) (350897309 / 100000000) (1755364567 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3539 / 64000) (711 / 12800) (350897309 / 100000000) (1755364567 / 500000000) (13332117 / 500000000000) (26805077 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (350897309 / 100000000) (1755364567 / 500000000) (386159239 / 200000000) (1931432031 / 1000000000) (13332117 / 500000000000) (26805077 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0884 :
    ∀ t ∈ Set.Icc ((711 / 12800) : ℝ) (3571 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1117499667537 / 1000000000000) : ℝ) ≤ Real.exp (2 * (711 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (711 / 12800)) (1117499667537 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3571 / 64000) : ℝ)) ≤ (1118058557083 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3571 / 64000)) (1118058557083 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((15451453 / 8000000) : ℝ) ≤ Real.exp (3 * (702145603 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (702145603 / 200000000) / 16) (15451453 / 8000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3512484937 / 1000000000) : ℝ) / 16) ≤ (1932067989 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3512484937 / 1000000000) / 16) (1932067989 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((711 / 12800) : ℝ) (3571 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (702145603 / 200000000) (3512484937 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (711 / 12800) (3571 / 64000) (1117499667537 / 1000000000000) (1118058557083 / 1000000000000) (702145603 / 200000000) (3512484937 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (711 / 12800) (3571 / 64000) (702145603 / 200000000) (3512484937 / 1000000000) (3315519 / 125000000000) (1066573 / 40000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (702145603 / 200000000) (3512484937 / 1000000000) (15451453 / 8000000) (1932067989 / 1000000000) (3315519 / 125000000000) (1066573 / 40000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0885 :
    ∀ t ∈ Set.Icc ((3571 / 64000) : ℝ) (3587 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((559029278541 / 500000000000) : ℝ) ≤ Real.exp (2 * (3571 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3571 / 64000)) (559029278541 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3587 / 64000) : ℝ)) ≤ (559308863071 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3587 / 64000)) (559308863071 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((966033791 / 500000000) : ℝ) ≤ Real.exp (3 * (1756241909 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1756241909 / 500000000) / 16) (966033791 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3514241619 / 1000000000) : ℝ) / 16) ≤ (966352237 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3514241619 / 1000000000) / 16) (966352237 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3571 / 64000) : ℝ) (3587 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1756241909 / 500000000) (3514241619 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3571 / 64000) (3587 / 64000) (559029278541 / 500000000000) (559308863071 / 500000000000) (1756241909 / 500000000) (3514241619 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3571 / 64000) (3587 / 64000) (1756241909 / 500000000) (3514241619 / 1000000000) (824523 / 31250000000) (26524243 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1756241909 / 500000000) (3514241619 / 1000000000) (966033791 / 500000000) (966352237 / 500000000) (824523 / 31250000000) (26524243 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0886 :
    ∀ t ∈ Set.Icc ((3587 / 64000) : ℝ) (3603 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1118617726141 / 1000000000000) : ℝ) ≤ Real.exp (2 * (3587 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3587 / 64000)) (1118617726141 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3603 / 64000) : ℝ)) ≤ (223835434971 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3603 / 64000)) (223835434971 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1932704067 / 1000000000) : ℝ) ≤ Real.exp (3 * (3514240499 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3514240499 / 1000000000) / 16) (1932704067 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3515999179 / 1000000000) : ℝ) / 16) ≤ (1933341487 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3515999179 / 1000000000) / 16) (1933341487 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3587 / 64000) : ℝ) (3603 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3514240499 / 1000000000) (3515999179 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3587 / 64000) (3603 / 64000) (1118617726141 / 1000000000000) (223835434971 / 200000000000) (3514240499 / 1000000000) (3515999179 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3587 / 64000) (3603 / 64000) (3514240499 / 1000000000) (3515999179 / 1000000000) (820187 / 31250000000) (13192413 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3514240499 / 1000000000) (3515999179 / 1000000000) (1932704067 / 1000000000) (1933341487 / 1000000000) (820187 / 31250000000) (13192413 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0887 :
    ∀ t ∈ Set.Icc ((3603 / 64000) : ℝ) (3619 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((559588587427 / 500000000000) : ℝ) ≤ Real.exp (2 * (3603 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3603 / 64000)) (559588587427 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3619 / 64000) : ℝ)) ≤ (1119736903363 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3619 / 64000)) (1119736903363 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((48333527 / 25000000) : ℝ) ≤ Real.exp (3 * (3515998059 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3515998059 / 1000000000) / 16) (48333527 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1758878809 / 500000000) : ℝ) / 16) ≤ (1933979029 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1758878809 / 500000000) / 16) (1933979029 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3603 / 64000) : ℝ) (3619 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3515998059 / 1000000000) (1758878809 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3603 / 64000) (3619 / 64000) (559588587427 / 500000000000) (1119736903363 / 1000000000000) (3515998059 / 1000000000) (1758878809 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3603 / 64000) (3619 / 64000) (3515998059 / 1000000000) (1758878809 / 500000000) (26107893 / 1000000000000) (13123037 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3515998059 / 1000000000) (1758878809 / 500000000) (48333527 / 25000000) (1933979029 / 1000000000) (26107893 / 1000000000000) (13123037 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0888 :
    ∀ t ∈ Set.Icc ((3619 / 64000) : ℝ) (727 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((559868451681 / 500000000000) : ℝ) ≤ Real.exp (2 * (3619 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3619 / 64000)) (559868451681 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((727 / 12800) : ℝ)) ≤ (224059382361 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (727 / 12800)) (224059382361 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1933978621 / 1000000000) : ℝ) ≤ Real.exp (3 * (3517756497 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3517756497 / 1000000000) / 16) (1933978621 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3519516937 / 1000000000) : ℝ) / 16) ≤ (19346171 / 10000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3519516937 / 1000000000) / 16) (19346171 / 10000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3619 / 64000) : ℝ) (727 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3517756497 / 1000000000) (3519516937 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3619 / 64000) (727 / 12800) (559868451681 / 500000000000) (224059382361 / 200000000000) (3517756497 / 1000000000) (3519516937 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3619 / 64000) (727 / 12800) (3517756497 / 1000000000) (3519516937 / 1000000000) (1298523 / 50000000000) (13053991 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3517756497 / 1000000000) (3519516937 / 1000000000) (1933978621 / 1000000000) (19346171 / 10000000) (1298523 / 50000000000) (13053991 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0889 :
    ∀ t ∈ Set.Icc ((727 / 12800) : ℝ) (3651 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((280074227951 / 250000000000) : ℝ) ≤ Real.exp (2 * (727 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (727 / 12800)) (280074227951 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3651 / 64000) : ℝ)) ≤ (560428600161 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3651 / 64000)) (560428600161 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((483654173 / 250000000) : ℝ) ≤ Real.exp (3 * (703903163 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (703903163 / 200000000) / 16) (483654173 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((704255427 / 200000000) : ℝ) / 16) ≤ (1935255701 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (704255427 / 200000000) / 16) (1935255701 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((727 / 12800) : ℝ) (3651 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (703903163 / 200000000) (704255427 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (727 / 12800) (3651 / 64000) (280074227951 / 250000000000) (560428600161 / 500000000000) (703903163 / 200000000) (704255427 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (727 / 12800) (3651 / 64000) (703903163 / 200000000) (704255427 / 200000000) (12916841 / 500000000000) (6492637 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (703903163 / 200000000) (704255427 / 200000000) (483654173 / 250000000) (1935255701 / 1000000000) (12916841 / 500000000000) (6492637 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0890 :
    ∀ t ∈ Set.Icc ((3651 / 64000) : ℝ) (3667 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1120857200321 / 1000000000000) : ℝ) ≤ Real.exp (2 * (3651 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3651 / 64000)) (1120857200321 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3667 / 64000) : ℝ)) ≤ (280354442263 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3667 / 64000)) (280354442263 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1935255293 / 1000000000) : ℝ) ≤ Real.exp (3 * (3521276013 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3521276013 / 1000000000) / 16) (1935255293 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1761519107 / 500000000) : ℝ) / 16) ≤ (1935894833 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1761519107 / 500000000) / 16) (1935894833 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3651 / 64000) : ℝ) (3667 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3521276013 / 1000000000) (1761519107 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3651 / 64000) (3667 / 64000) (1120857200321 / 1000000000000) (280354442263 / 250000000000) (3521276013 / 1000000000) (1761519107 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3651 / 64000) (3667 / 64000) (3521276013 / 1000000000) (1761519107 / 500000000) (6424389 / 250000000000) (2583377 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3521276013 / 1000000000) (1761519107 / 500000000) (1935255293 / 1000000000) (1935894833 / 1000000000) (6424389 / 250000000000) (2583377 / 100000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0891 :
    ∀ t ∈ Set.Icc ((3667 / 64000) : ℝ) (3683 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1121417769051 / 1000000000000) : ℝ) ≤ Real.exp (2 * (3667 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3667 / 64000)) (1121417769051 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3683 / 64000) : ℝ)) ≤ (1121978618137 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3683 / 64000)) (1121978618137 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((241986803 / 125000000) : ℝ) ≤ Real.exp (3 * (3523037091 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3523037091 / 1000000000) / 16) (241986803 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3524800173 / 1000000000) : ℝ) / 16) ≤ (387306899 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3524800173 / 1000000000) / 16) (387306899 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3667 / 64000) : ℝ) (3683 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3523037091 / 1000000000) (3524800173 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3667 / 64000) (3683 / 64000) (1121417769051 / 1000000000000) (1121978618137 / 1000000000000) (3523037091 / 1000000000) (3524800173 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3667 / 64000) (3683 / 64000) (3523037091 / 1000000000) (3524800173 / 1000000000) (159763 / 6250000000) (6424411 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3523037091 / 1000000000) (3524800173 / 1000000000) (241986803 / 125000000) (387306899 / 200000000) (159763 / 6250000000) (6424411 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0892 :
    ∀ t ∈ Set.Icc ((3683 / 64000) : ℝ) (3699 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((140247327267 / 125000000000) : ℝ) ≤ Real.exp (2 * (3683 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3683 / 64000)) (140247327267 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3699 / 64000) : ℝ)) ≤ (1122539747717 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3699 / 64000)) (1122539747717 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((968267043 / 500000000) : ℝ) ≤ Real.exp (3 * (70495981 / 20000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (70495981 / 20000000) / 16) (968267043 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1763281507 / 500000000) : ℝ) / 16) ≤ (60536709 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1763281507 / 500000000) / 16) (60536709 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3683 / 64000) : ℝ) (3699 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (70495981 / 20000000) (1763281507 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3683 / 64000) (3699 / 64000) (140247327267 / 125000000000) (1122539747717 / 1000000000000) (70495981 / 20000000) (1763281507 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3683 / 64000) (3699 / 64000) (70495981 / 20000000) (1763281507 / 500000000) (6356813 / 250000000000) (3195271 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (70495981 / 20000000) (1763281507 / 500000000) (968267043 / 500000000) (60536709 / 31250000) (6356813 / 250000000000) (3195271 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0893 :
    ∀ t ∈ Set.Icc ((3699 / 64000) : ℝ) (743 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((280634936929 / 250000000000) : ℝ) ≤ Real.exp (2 * (3699 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3699 / 64000)) (280634936929 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((743 / 12800) : ℝ)) ≤ (280775289483 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (743 / 12800)) (280775289483 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1937174279 / 1000000000) : ℝ) ≤ Real.exp (3 * (3526561891 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3526561891 / 1000000000) / 16) (1937174279 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3528326737 / 1000000000) : ℝ) / 16) ≤ (968907707 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3528326737 / 1000000000) / 16) (968907707 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3699 / 64000) : ℝ) (743 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3526561891 / 1000000000) (3528326737 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3699 / 64000) (743 / 12800) (280634936929 / 250000000000) (280775289483 / 250000000000) (3526561891 / 1000000000) (3528326737 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3699 / 64000) (743 / 12800) (3526561891 / 1000000000) (3528326737 / 1000000000) (25293067 / 1000000000000) (12713669 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3526561891 / 1000000000) (3528326737 / 1000000000) (1937174279 / 1000000000) (968907707 / 500000000) (25293067 / 1000000000000) (12713669 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0894 :
    ∀ t ∈ Set.Icc ((743 / 12800) : ℝ) (3731 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1123101157931 / 1000000000000) : ℝ) ≤ Real.exp (2 * (743 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (743 / 12800)) (1123101157931 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3731 / 64000) : ℝ)) ≤ (561831424461 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3731 / 64000)) (561831424461 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((484453751 / 250000000) : ℝ) ≤ Real.exp (3 * (882081403 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (882081403 / 250000000) / 16) (484453751 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3530091341 / 1000000000) : ℝ) / 16) ≤ (60576771 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3530091341 / 1000000000) / 16) (60576771 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((743 / 12800) : ℝ) (3731 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (882081403 / 250000000) (3530091341 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (743 / 12800) (3731 / 64000) (1123101157931 / 1000000000000) (561831424461 / 500000000000) (882081403 / 250000000) (3530091341 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (743 / 12800) (3731 / 64000) (882081403 / 250000000) (3530091341 / 1000000000) (6289881 / 250000000000) (12646577 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (882081403 / 250000000) (3530091341 / 1000000000) (484453751 / 250000000) (60576771 / 31250000) (6289881 / 250000000000) (12646577 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0895 :
    ∀ t ∈ Set.Icc ((3731 / 64000) : ℝ) (3747 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1123662848921 / 1000000000000) : ℝ) ≤ Real.exp (2 * (3731 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3731 / 64000)) (1123662848921 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3747 / 64000) : ℝ)) ≤ (281056205207 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3747 / 64000)) (281056205207 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((969228131 / 500000000) : ℝ) ≤ Real.exp (3 * (441261277 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (441261277 / 125000000) / 16) (969228131 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((882964207 / 250000000) : ℝ) / 16) ≤ (1939098463 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (882964207 / 250000000) / 16) (1939098463 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3731 / 64000) : ℝ) (3747 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (441261277 / 125000000) (882964207 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3731 / 64000) (3747 / 64000) (1123662848921 / 1000000000000) (281056205207 / 250000000000) (441261277 / 125000000) (882964207 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3731 / 64000) (3747 / 64000) (441261277 / 125000000) (882964207 / 250000000) (1251331 / 50000000000) (2515961 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (441261277 / 125000000) (882964207 / 250000000) (969228131 / 500000000) (1939098463 / 1000000000) (1251331 / 50000000000) (2515961 / 100000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0896 :
    ∀ t ∈ Set.Icc ((3747 / 64000) : ℝ) (3763 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1124224820827 / 1000000000000) : ℝ) ≤ Real.exp (2 * (3747 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3747 / 64000)) (1124224820827 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3763 / 64000) : ℝ)) ≤ (112478707379 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3763 / 64000)) (112478707379 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1939098053 / 1000000000) : ℝ) ≤ Real.exp (3 * (3531855703 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3531855703 / 1000000000) / 16) (1939098053 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1766811599 / 500000000) : ℝ) / 16) ≤ (484935197 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1766811599 / 500000000) / 16) (484935197 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3747 / 64000) : ℝ) (3763 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3531855703 / 1000000000) (1766811599 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3747 / 64000) (3763 / 64000) (1124224820827 / 1000000000000) (112478707379 / 100000000000) (3531855703 / 1000000000) (1766811599 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3747 / 64000) (3763 / 64000) (3531855703 / 1000000000) (1766811599 / 500000000) (1555897 / 62500000000) (12513353 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3531855703 / 1000000000) (1766811599 / 500000000) (1939098053 / 1000000000) (484935197 / 250000000) (1555897 / 62500000000) (12513353 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0897 :
    ∀ t ∈ Set.Icc ((3763 / 64000) : ℝ) (3779 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1124787073789 / 1000000000000) : ℝ) ≤ Real.exp (2 * (3763 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3763 / 64000)) (1124787073789 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3779 / 64000) : ℝ)) ≤ (281337401987 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3779 / 64000)) (281337401987 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((969870189 / 500000000) : ℝ) ≤ Real.exp (3 * (441702759 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (441702759 / 125000000) / 16) (969870189 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3535390451 / 1000000000) : ℝ) / 16) ≤ (1940383647 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3535390451 / 1000000000) / 16) (1940383647 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3763 / 64000) : ℝ) (3779 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (441702759 / 125000000) (3535390451 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3763 / 64000) (3779 / 64000) (1124787073789 / 1000000000000) (281337401987 / 250000000000) (441702759 / 125000000) (3535390451 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3763 / 64000) (3779 / 64000) (441702759 / 125000000) (3535390451 / 1000000000) (24762717 / 1000000000000) (24894437 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (441702759 / 125000000) (3535390451 / 1000000000) (969870189 / 500000000) (1940383647 / 1000000000) (24762717 / 1000000000000) (24894437 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0898 :
    ∀ t ∈ Set.Icc ((3779 / 64000) : ℝ) (759 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1125349607947 / 1000000000000) : ℝ) ≤ Real.exp (2 * (3779 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3779 / 64000)) (1125349607947 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((759 / 12800) : ℝ)) ≤ (281478105861 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (759 / 12800)) (281478105861 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1940383237 / 1000000000) : ℝ) ≤ Real.exp (3 * (141415573 / 40000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (141415573 / 40000000) / 16) (1940383237 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3537158589 / 1000000000) : ℝ) / 16) ≤ (1941027041 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3537158589 / 1000000000) / 16) (1941027041 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3779 / 64000) : ℝ) (759 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (141415573 / 40000000) (3537158589 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3779 / 64000) (759 / 12800) (1125349607947 / 1000000000000) (281478105861 / 250000000000) (141415573 / 40000000) (3537158589 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3779 / 64000) (759 / 12800) (141415573 / 40000000) (3537158589 / 1000000000) (24631713 / 1000000000000) (12381401 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (141415573 / 40000000) (3537158589 / 1000000000) (1940383237 / 1000000000) (1941027041 / 1000000000) (24631713 / 1000000000000) (12381401 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0899 :
    ∀ t ∈ Set.Icc ((759 / 12800) : ℝ) (3811 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1125912423443 / 1000000000000) : ℝ) ≤ Real.exp (2 * (759 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (759 / 12800)) (1125912423443 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3811 / 64000) : ℝ)) ≤ (1126475520419 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3811 / 64000)) (1126475520419 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((194102663 / 100000000) : ℝ) ≤ Real.exp (3 * (1768578731 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1768578731 / 500000000) / 16) (194102663 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((353892761 / 100000000) : ℝ) / 16) ≤ (194167097 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (353892761 / 100000000) / 16) (194167097 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((759 / 12800) : ℝ) (3811 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1768578731 / 500000000) (353892761 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (759 / 12800) (3811 / 64000) (1125912423443 / 1000000000000) (1126475520419 / 1000000000000) (1768578731 / 500000000) (353892761 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (759 / 12800) (3811 / 64000) (1768578731 / 500000000) (353892761 / 100000000) (24501337 / 1000000000000) (12315899 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1768578731 / 500000000) (353892761 / 100000000) (194102663 / 100000000) (194167097 / 100000000) (24501337 / 1000000000000) (12315899 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch044 :
    ∀ t ∈ Set.Icc ((3499 / 64000) : ℝ) (3811 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0880
      hpThetaDensityTwoTermCompact_cell0881)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0882
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0883
      hpThetaDensityTwoTermCompact_cell0884)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0885
      hpThetaDensityTwoTermCompact_cell0886)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0887
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0888
      hpThetaDensityTwoTermCompact_cell0889))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0890
      hpThetaDensityTwoTermCompact_cell0891)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0892
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0893
      hpThetaDensityTwoTermCompact_cell0894)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0895
      hpThetaDensityTwoTermCompact_cell0896)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0897
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0898
      hpThetaDensityTwoTermCompact_cell0899)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch044
end HodgeProofHP
