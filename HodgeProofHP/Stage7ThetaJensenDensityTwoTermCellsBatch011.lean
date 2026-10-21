/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0220 :
    ∀ t ∈ Set.Icc ((1469 / 64000) : ℝ) (147 / 6400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((261744063083 / 250000000000) : ℝ) ≤ Real.exp (2 * (1469 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1469 / 64000)) (261744063083 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((147 / 6400) : ℝ)) ≤ (261752242713 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (147 / 6400)) (261752242713 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1852840359 / 1000000000) : ℝ) ≤ Real.exp (3 * (1644586109 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1644586109 / 500000000) / 16) (1852840359 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1644638027 / 500000000) : ℝ) / 16) ≤ (1852876433 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1644638027 / 500000000) / 16) (1852876433 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1469 / 64000) : ℝ) (147 / 6400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1644586109 / 500000000) (1644638027 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1469 / 64000) (147 / 6400) (261744063083 / 250000000000) (261752242713 / 250000000000) (1644586109 / 500000000) (1644638027 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1469 / 64000) (147 / 6400) (1644586109 / 500000000) (1644638027 / 500000000) (2590757 / 50000000000) (12957821 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1644586109 / 500000000) (1644638027 / 500000000) (1852840359 / 1000000000) (1852876433 / 1000000000) (2590757 / 50000000000) (12957821 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0221 :
    ∀ t ∈ Set.Icc ((147 / 6400) : ℝ) (1471 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1047008970851 / 1000000000000) : ℝ) ≤ Real.exp (2 * (147 / 6400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (147 / 6400)) (1047008970851 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1471 / 64000) : ℝ)) ≤ (1047041690393 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1471 / 64000)) (1047041690393 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((463219017 / 250000000) : ℝ) ≤ Real.exp (3 * (1644637503 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1644637503 / 500000000) / 16) (463219017 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1644689423 / 500000000) : ℝ) / 16) ≤ (370582429 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1644689423 / 500000000) / 16) (370582429 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((147 / 6400) : ℝ) (1471 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1644637503 / 500000000) (1644689423 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (147 / 6400) (1471 / 64000) (1047008970851 / 1000000000000) (1047041690393 / 1000000000000) (1644637503 / 500000000) (1644689423 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (147 / 6400) (1471 / 64000) (1644637503 / 500000000) (1644689423 / 500000000) (12949791 / 250000000000) (6476913 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1644637503 / 500000000) (1644689423 / 500000000) (463219017 / 250000000) (370582429 / 200000000) (12949791 / 250000000000) (6476913 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0222 :
    ∀ t ∈ Set.Icc ((1471 / 64000) : ℝ) (23 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((130880211299 / 125000000000) : ℝ) ≤ Real.exp (2 * (1471 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1471 / 64000)) (130880211299 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((23 / 1000) : ℝ)) ≤ (1047074410957 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (23 / 1000)) (1047074410957 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((92645589 / 50000000) : ℝ) ≤ Real.exp (3 * (1644688899 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1644688899 / 500000000) / 16) (92645589 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((82237041 / 25000000) : ℝ) / 16) ≤ (926473929 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (82237041 / 25000000) / 16) (926473929 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1471 / 64000) : ℝ) (23 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1644688899 / 500000000) (82237041 / 25000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1471 / 64000) (23 / 1000) (130880211299 / 125000000000) (1047074410957 / 1000000000000) (1644688899 / 500000000) (82237041 / 25000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1471 / 64000) (23 / 1000) (1644688899 / 500000000) (82237041 / 25000000) (6472899 / 125000000000) (1618729 / 31250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1644688899 / 500000000) (82237041 / 25000000) (92645589 / 50000000) (926473929 / 500000000) (6472899 / 125000000000) (1618729 / 31250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0223 :
    ∀ t ∈ Set.Icc ((23 / 1000) : ℝ) (1473 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((261768602739 / 250000000000) : ℝ) ≤ Real.exp (2 * (23 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (23 / 1000)) (261768602739 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1473 / 64000) : ℝ)) ≤ (8180524473 / 7812500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1473 / 64000)) (8180524473 / 7812500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1852947493 / 1000000000) : ℝ) ≤ Real.exp (3 * (205592537 / 62500000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (205592537 / 62500000) / 16) (1852947493 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1644792219 / 500000000) : ℝ) / 16) ≤ (1852983573 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1644792219 / 500000000) / 16) (1852983573 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((23 / 1000) : ℝ) (1473 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (205592537 / 62500000) (1644792219 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (23 / 1000) (1473 / 64000) (261768602739 / 250000000000) (8180524473 / 7812500000) (205592537 / 62500000) (1644792219 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (23 / 1000) (1473 / 64000) (205592537 / 62500000) (1644792219 / 500000000) (2070689 / 40000000000) (51783357 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (205592537 / 62500000) (1644792219 / 500000000) (1852947493 / 1000000000) (1852983573 / 1000000000) (2070689 / 40000000000) (51783357 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0224 :
    ∀ t ∈ Set.Icc ((1473 / 64000) : ℝ) (737 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1047107132543 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1473 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1473 / 64000)) (1047107132543 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((737 / 32000) : ℝ)) ≤ (1047139855153 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (737 / 32000)) (1047139855153 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((231622901 / 125000000) : ℝ) ≤ Real.exp (3 * (328958339 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (328958339 / 100000000) / 16) (231622901 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3289687239 / 1000000000) : ℝ) / 16) ≤ (185301929 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3289687239 / 1000000000) / 16) (185301929 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1473 / 64000) : ℝ) (737 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (328958339 / 100000000) (3289687239 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1473 / 64000) (737 / 32000) (1047107132543 / 1000000000000) (1047139855153 / 1000000000000) (328958339 / 100000000) (3289687239 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1473 / 64000) (737 / 32000) (328958339 / 100000000) (3289687239 / 1000000000) (51751263 / 1000000000000) (51767389 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (328958339 / 100000000) (3289687239 / 1000000000) (231622901 / 125000000) (185301929 / 100000000) (51751263 / 1000000000000) (51767389 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0225 :
    ∀ t ∈ Set.Icc ((737 / 32000) : ℝ) (59 / 2560), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((65446240947 / 62500000000) : ℝ) ≤ Real.exp (2 * (737 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (737 / 32000)) (65446240947 / 62500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((59 / 2560) : ℝ)) ≤ (209434515757 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (59 / 2560)) (209434515757 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((74120757 / 40000000) : ℝ) ≤ Real.exp (3 * (3289686191 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3289686191 / 1000000000) / 16) (74120757 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((822447511 / 250000000) : ℝ) / 16) ≤ (1853055009 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (822447511 / 250000000) / 16) (1853055009 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((737 / 32000) : ℝ) (59 / 2560),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3289686191 / 1000000000) (822447511 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (737 / 32000) (59 / 2560) (65446240947 / 62500000000) (209434515757 / 200000000000) (3289686191 / 1000000000) (822447511 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (737 / 32000) (59 / 2560) (3289686191 / 1000000000) (822447511 / 250000000) (6466913 / 125000000000) (51751427 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3289686191 / 1000000000) (822447511 / 250000000) (74120757 / 40000000) (1853055009 / 1000000000) (6466913 / 125000000000) (51751427 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0226 :
    ∀ t ∈ Set.Icc ((59 / 2560) : ℝ) (369 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((32724143087 / 31250000000) : ℝ) ≤ Real.exp (2 * (59 / 2560)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (59 / 2560)) (32724143087 / 31250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((369 / 16000) : ℝ)) ≤ (1047205303439 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (369 / 16000)) (1047205303439 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((463263661 / 250000000) : ℝ) ≤ Real.exp (3 * (822447249 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (822447249 / 250000000) / 16) (463263661 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3289892851 / 1000000000) : ℝ) / 16) ≤ (185309073 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3289892851 / 1000000000) / 16) (185309073 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((59 / 2560) : ℝ) (369 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (822447249 / 250000000) (3289892851 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (59 / 2560) (369 / 16000) (32724143087 / 31250000000) (1047205303439 / 1000000000000) (822447249 / 250000000) (3289892851 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (59 / 2560) (369 / 16000) (822447249 / 250000000) (3289892851 / 1000000000) (1034387 / 20000000000) (12933867 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (822447249 / 250000000) (3289892851 / 1000000000) (463263661 / 250000000) (185309073 / 100000000) (1034387 / 20000000000) (12933867 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0227 :
    ∀ t ∈ Set.Icc ((369 / 16000) : ℝ) (1477 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((523602651719 / 500000000000) : ℝ) ≤ Real.exp (2 * (369 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (369 / 16000)) (523602651719 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1477 / 64000) : ℝ)) ≤ (261809507279 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1477 / 64000)) (261809507279 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((370618073 / 200000000) : ℝ) ≤ Real.exp (3 * (3289891803 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3289891803 / 1000000000) / 16) (370618073 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1644997831 / 500000000) : ℝ) / 16) ≤ (463281613 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1644997831 / 500000000) / 16) (463281613 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((369 / 16000) : ℝ) (1477 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3289891803 / 1000000000) (1644997831 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (369 / 16000) (1477 / 64000) (523602651719 / 500000000000) (261809507279 / 250000000000) (3289891803 / 1000000000) (1644997831 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (369 / 16000) (1477 / 64000) (3289891803 / 1000000000) (1644997831 / 500000000) (51703401 / 1000000000000) (25859757 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3289891803 / 1000000000) (1644997831 / 500000000) (370618073 / 200000000) (463281613 / 250000000) (51703401 / 1000000000000) (25859757 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0228 :
    ∀ t ∈ Set.Icc ((1477 / 64000) : ℝ) (739 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((209447605823 / 200000000000) : ℝ) ≤ Real.exp (2 * (1477 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1477 / 64000)) (209447605823 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((739 / 32000) : ℝ)) ≤ (130908844477 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (739 / 32000)) (130908844477 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1853126087 / 1000000000) : ℝ) ≤ Real.exp (3 * (1644997307 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1644997307 / 500000000) / 16) (1853126087 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((822524619 / 250000000) : ℝ) / 16) ≤ (28955659 / 15625000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (822524619 / 250000000) / 16) (28955659 / 15625000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1477 / 64000) : ℝ) (739 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1644997307 / 500000000) (822524619 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1477 / 64000) (739 / 32000) (209447605823 / 200000000000) (130908844477 / 125000000000) (1644997307 / 500000000) (822524619 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1477 / 64000) (739 / 32000) (1644997307 / 500000000) (822524619 / 250000000) (1615233 / 31250000000) (10340713 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1644997307 / 500000000) (822524619 / 250000000) (1853126087 / 1000000000) (28955659 / 15625000) (1615233 / 31250000000) (10340713 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0229 :
    ∀ t ∈ Set.Icc ((739 / 32000) : ℝ) (1479 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((209454151163 / 200000000000) : ℝ) ≤ Real.exp (2 * (739 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (739 / 32000)) (209454151163 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1479 / 64000) : ℝ)) ≤ (1047303483539 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1479 / 64000)) (1047303483539 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1853161811 / 1000000000) : ℝ) ≤ Real.exp (3 * (822524357 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (822524357 / 250000000) / 16) (1853161811 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3290201293 / 1000000000) : ℝ) / 16) ≤ (926598951 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3290201293 / 1000000000) / 16) (926598951 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((739 / 32000) : ℝ) (1479 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (822524357 / 250000000) (3290201293 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (739 / 32000) (1479 / 64000) (209454151163 / 200000000000) (1047303483539 / 1000000000000) (822524357 / 250000000) (3290201293 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (739 / 32000) (1479 / 64000) (822524357 / 250000000) (3290201293 / 1000000000) (10334303 / 200000000000) (2584381 / 50000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (822524357 / 250000000) (3290201293 / 1000000000) (1853161811 / 1000000000) (926598951 / 500000000) (10334303 / 200000000000) (2584381 / 50000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0230 :
    ∀ t ∈ Set.Icc ((1479 / 64000) : ℝ) (37 / 1600), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((523651741769 / 500000000000) : ℝ) ≤ Real.exp (2 * (1479 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1479 / 64000)) (523651741769 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((37 / 1600) : ℝ)) ≤ (261834053071 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (37 / 1600)) (261834053071 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1853197537 / 1000000000) : ℝ) ≤ Real.exp (3 * (658040049 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (658040049 / 200000000) / 16) (1853197537 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1645152057 / 500000000) : ℝ) / 16) ≤ (185323363 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1645152057 / 500000000) / 16) (185323363 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1479 / 64000) : ℝ) (37 / 1600),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (658040049 / 200000000) (1645152057 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1479 / 64000) (37 / 1600) (523651741769 / 500000000000) (261834053071 / 250000000000) (658040049 / 200000000) (1645152057 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1479 / 64000) (37 / 1600) (658040049 / 200000000) (1645152057 / 500000000) (51655579 / 1000000000000) (51671679 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (658040049 / 200000000) (1645152057 / 500000000) (1853197537 / 1000000000) (185323363 / 100000000) (51655579 / 1000000000000) (51671679 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0231 :
    ∀ t ∈ Set.Icc ((37 / 1600) : ℝ) (1481 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1047336212283 / 1000000000000) : ℝ) ≤ Real.exp (2 * (37 / 1600)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (37 / 1600)) (1047336212283 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1481 / 64000) : ℝ)) ≤ (261842235513 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1481 / 64000)) (261842235513 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((370646653 / 200000000) : ℝ) ≤ Real.exp (3 * (658060613 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (658060613 / 200000000) / 16) (370646653 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3290406937 / 1000000000) : ℝ) / 16) ≤ (23165867 / 12500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3290406937 / 1000000000) / 16) (23165867 / 12500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((37 / 1600) : ℝ) (1481 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (658060613 / 200000000) (3290406937 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (37 / 1600) (1481 / 64000) (1047336212283 / 1000000000000) (261842235513 / 250000000000) (658060613 / 200000000) (3290406937 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (37 / 1600) (1481 / 64000) (658060613 / 200000000) (3290406937 / 1000000000) (51639647 / 1000000000000) (51655743 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (658060613 / 200000000) (3290406937 / 1000000000) (370646653 / 200000000) (23165867 / 12500000) (51639647 / 1000000000000) (51655743 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0232 :
    ∀ t ∈ Set.Icc ((1481 / 64000) : ℝ) (741 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1047368942051 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1481 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1481 / 64000)) (1047368942051 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((741 / 32000) : ℝ)) ≤ (1047401672843 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (741 / 32000)) (1047401672843 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((370653799 / 200000000) : ℝ) ≤ Real.exp (3 * (3290405889 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3290405889 / 1000000000) / 16) (370653799 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((822627441 / 250000000) : ℝ) / 16) ≤ (1853305091 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (822627441 / 250000000) / 16) (1853305091 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1481 / 64000) : ℝ) (741 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3290405889 / 1000000000) (822627441 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1481 / 64000) (741 / 32000) (1047368942051 / 1000000000000) (1047401672843 / 1000000000000) (3290405889 / 1000000000) (822627441 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1481 / 64000) (741 / 32000) (3290405889 / 1000000000) (822627441 / 250000000) (1290593 / 25000000000) (51639811 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3290405889 / 1000000000) (822627441 / 250000000) (370653799 / 200000000) (1853305091 / 1000000000) (1290593 / 25000000000) (51639811 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0233 :
    ∀ t ∈ Set.Icc ((741 / 32000) : ℝ) (1483 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((523700836421 / 500000000000) : ℝ) ≤ Real.exp (2 * (741 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (741 / 32000)) (523700836421 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1483 / 64000) : ℝ)) ≤ (1047434404657 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1483 / 64000)) (1047434404657 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((926652363 / 500000000) : ℝ) ≤ Real.exp (3 * (822627179 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (822627179 / 250000000) / 16) (926652363 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1645306297 / 500000000) : ℝ) / 16) ≤ (74133633 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1645306297 / 500000000) / 16) (74133633 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((741 / 32000) : ℝ) (1483 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (822627179 / 250000000) (1645306297 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (741 / 32000) (1483 / 64000) (523700836421 / 500000000000) (1047434404657 / 1000000000000) (822627179 / 250000000) (1645306297 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (741 / 32000) (1483 / 64000) (822627179 / 250000000) (1645306297 / 500000000) (51607797 / 1000000000000) (12905971 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (822627179 / 250000000) (1645306297 / 500000000) (926652363 / 500000000) (74133633 / 40000000) (51607797 / 1000000000000) (12905971 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0234 :
    ∀ t ∈ Set.Icc ((1483 / 64000) : ℝ) (371 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((65464650291 / 62500000000) : ℝ) ≤ Real.exp (2 * (1483 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1483 / 64000)) (65464650291 / 62500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((371 / 16000) : ℝ)) ≤ (1047467137493 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (371 / 16000)) (1047467137493 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1853340459 / 1000000000) : ℝ) ≤ Real.exp (3 * (1645305773 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1645305773 / 500000000) / 16) (1853340459 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3290715427 / 1000000000) : ℝ) / 16) ≤ (23167207 / 12500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3290715427 / 1000000000) / 16) (23167207 / 12500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1483 / 64000) : ℝ) (371 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1645305773 / 500000000) (3290715427 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1483 / 64000) (371 / 16000) (65464650291 / 62500000000) (1047467137493 / 1000000000000) (1645305773 / 500000000) (3290715427 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1483 / 64000) (371 / 16000) (1645305773 / 500000000) (3290715427 / 1000000000) (25795939 / 500000000000) (51607961 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1645305773 / 500000000) (3290715427 / 1000000000) (1853340459 / 1000000000) (23167207 / 12500000) (25795939 / 500000000000) (51607961 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0235 :
    ∀ t ∈ Set.Icc ((371 / 16000) : ℝ) (297 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((261866784373 / 250000000000) : ℝ) ≤ Real.exp (2 * (371 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (371 / 16000)) (261866784373 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((297 / 12800) : ℝ)) ≤ (1047499871353 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (297 / 12800)) (1047499871353 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((926688097 / 500000000) : ℝ) ≤ Real.exp (3 * (3290714379 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3290714379 / 1000000000) / 16) (926688097 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((411352283 / 125000000) : ℝ) / 16) ≤ (1853412297 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (411352283 / 125000000) / 16) (1853412297 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((371 / 16000) : ℝ) (297 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3290714379 / 1000000000) (411352283 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (371 / 16000) (297 / 12800) (261866784373 / 250000000000) (1047499871353 / 1000000000000) (3290714379 / 1000000000) (411352283 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (371 / 16000) (297 / 12800) (3290714379 / 1000000000) (411352283 / 125000000) (12893991 / 250000000000) (25796021 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3290714379 / 1000000000) (411352283 / 125000000) (926688097 / 500000000) (1853412297 / 1000000000) (12893991 / 250000000000) (25796021 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0236 :
    ∀ t ∈ Set.Icc ((297 / 12800) : ℝ) (743 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((130937483919 / 125000000000) : ℝ) ≤ Real.exp (2 * (297 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (297 / 12800)) (130937483919 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((743 / 32000) : ℝ)) ≤ (209506521247 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (743 / 32000)) (209506521247 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1853411931 / 1000000000) : ℝ) ≤ Real.exp (3 * (658163443 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (658163443 / 200000000) / 16) (1853411931 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((205682569 / 62500000) : ℝ) / 16) ≤ (370689607 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (205682569 / 62500000) / 16) (370689607 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((297 / 12800) : ℝ) (743 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (658163443 / 200000000) (205682569 / 62500000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (297 / 12800) (743 / 32000) (130937483919 / 125000000000) (209506521247 / 200000000000) (658163443 / 200000000) (205682569 / 62500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (297 / 12800) (743 / 32000) (658163443 / 200000000) (205682569 / 62500000) (10312011 / 200000000000) (805877 / 15625000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (658163443 / 200000000) (205682569 / 62500000) (1853411931 / 1000000000) (370689607 / 200000000) (10312011 / 200000000000) (805877 / 15625000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0237 :
    ∀ t ∈ Set.Icc ((743 / 32000) : ℝ) (1487 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((523766303117 / 500000000000) : ℝ) ≤ Real.exp (2 * (743 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (743 / 32000)) (523766303117 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1487 / 64000) : ℝ)) ≤ (1047565342141 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1487 / 64000)) (1047565342141 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((185344767 / 100000000) : ℝ) ≤ Real.exp (3 * (658184011 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (658184011 / 200000000) / 16) (185344767 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1645511973 / 500000000) : ℝ) / 16) ≤ (7240171 / 3906250) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1645511973 / 500000000) / 16) (7240171 / 3906250) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((743 / 32000) : ℝ) (1487 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (658184011 / 200000000) (1645511973 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (743 / 32000) (1487 / 64000) (523766303117 / 500000000000) (1047565342141 / 1000000000000) (658184011 / 200000000) (1645511973 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (743 / 32000) (1487 / 64000) (658184011 / 200000000) (1645511973 / 500000000) (51544149 / 1000000000000) (25780109 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (658184011 / 200000000) (1645511973 / 500000000) (185344767 / 100000000) (7240171 / 3906250) (51544149 / 1000000000000) (25780109 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0238 :
    ∀ t ∈ Set.Icc ((1487 / 64000) : ℝ) (93 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((52378267107 / 50000000000) : ℝ) ≤ Real.exp (2 * (1487 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1487 / 64000)) (52378267107 / 50000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((93 / 4000) : ℝ)) ≤ (1047598079069 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (93 / 4000)) (1047598079069 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((185348341 / 100000000) : ℝ) ≤ Real.exp (3 * (1645511449 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1645511449 / 500000000) / 16) (185348341 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3291126793 / 1000000000) : ℝ) / 16) ≤ (926759759 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3291126793 / 1000000000) / 16) (926759759 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1487 / 64000) : ℝ) (93 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1645511449 / 500000000) (3291126793 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1487 / 64000) (93 / 4000) (52378267107 / 50000000000) (1047598079069 / 1000000000000) (1645511449 / 500000000) (3291126793 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1487 / 64000) (93 / 4000) (1645511449 / 500000000) (3291126793 / 1000000000) (6441031 / 125000000000) (51544313 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1645511449 / 500000000) (3291126793 / 1000000000) (185348341 / 100000000) (926759759 / 500000000) (6441031 / 125000000000) (51544313 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0239 :
    ∀ t ∈ Set.Icc ((93 / 4000) : ℝ) (1489 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((261899519767 / 250000000000) : ℝ) ≤ Real.exp (2 * (93 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (93 / 4000)) (261899519767 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1489 / 64000) : ℝ)) ≤ (1047630817021 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1489 / 64000)) (1047630817021 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1853519153 / 1000000000) : ℝ) ≤ Real.exp (3 * (205695359 / 62500000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (205695359 / 62500000) / 16) (1853519153 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1645614821 / 500000000) : ℝ) / 16) ≤ (926777631 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1645614821 / 500000000) / 16) (926777631 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((93 / 4000) : ℝ) (1489 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (205695359 / 62500000) (1645614821 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (93 / 4000) (1489 / 64000) (261899519767 / 250000000000) (1047630817021 / 1000000000000) (205695359 / 62500000) (1645614821 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (93 / 4000) (1489 / 64000) (205695359 / 62500000) (1645614821 / 500000000) (1609761 / 31250000000) (12882103 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (205695359 / 62500000) (1645614821 / 500000000) (1853519153 / 1000000000) (926777631 / 500000000) (1609761 / 31250000000) (12882103 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch011 :
    ∀ t ∈ Set.Icc ((1469 / 64000) : ℝ) (1489 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0220
      hpThetaDensityTwoTermCompact_cell0221)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0222
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0223
      hpThetaDensityTwoTermCompact_cell0224)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0225
      hpThetaDensityTwoTermCompact_cell0226)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0227
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0228
      hpThetaDensityTwoTermCompact_cell0229))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0230
      hpThetaDensityTwoTermCompact_cell0231)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0232
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0233
      hpThetaDensityTwoTermCompact_cell0234)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0235
      hpThetaDensityTwoTermCompact_cell0236)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0237
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0238
      hpThetaDensityTwoTermCompact_cell0239)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch011
end HodgeProofHP
