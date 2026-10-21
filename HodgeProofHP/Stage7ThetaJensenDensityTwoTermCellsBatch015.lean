/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0300 :
    ∀ t ∈ Set.Icc ((1549 / 64000) : ℝ) (31 / 1280), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1049596967491 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1549 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1549 / 64000)) (1049596967491 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((31 / 1280) : ℝ)) ≤ (104962976791 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (31 / 1280)) (104962976791 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((37114057 / 20000000) : ℝ) ≤ Real.exp (3 * (824351359 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (824351359 / 250000000) / 16) (37114057 / 20000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((824377383 / 250000000) : ℝ) / 16) ≤ (1855739071 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (824377383 / 250000000) / 16) (1855739071 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1549 / 64000) : ℝ) (31 / 1280),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (824351359 / 250000000) (824377383 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1549 / 64000) (31 / 1280) (1049596967491 / 1000000000000) (104962976791 / 100000000000) (824351359 / 250000000) (824377383 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1549 / 64000) (31 / 1280) (824351359 / 250000000) (824377383 / 250000000) (631887 / 12500000000) (50566751 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (824351359 / 250000000) (824377383 / 250000000) (37114057 / 20000000) (1855739071 / 1000000000) (631887 / 12500000000) (50566751 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0301 :
    ∀ t ∈ Set.Icc ((31 / 1280) : ℝ) (1551 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1049629767909 / 1000000000000) : ℝ) ≤ Real.exp (2 * (31 / 1280)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (31 / 1280)) (1049629767909 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1551 / 64000) : ℝ)) ≤ (1049662569353 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1551 / 64000)) (1049662569353 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((115983669 / 62500000) : ℝ) ≤ Real.exp (3 * (3297508481 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3297508481 / 1000000000) / 16) (115983669 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3297612581 / 1000000000) : ℝ) / 16) ≤ (1855774927 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3297612581 / 1000000000) / 16) (1855774927 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((31 / 1280) : ℝ) (1551 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3297508481 / 1000000000) (3297612581 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (31 / 1280) (1551 / 64000) (1049629767909 / 1000000000000) (1049662569353 / 1000000000000) (3297508481 / 1000000000) (3297612581 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (31 / 1280) (1551 / 64000) (3297508481 / 1000000000) (3297612581 / 1000000000) (10107067 / 200000000000) (50551121 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3297508481 / 1000000000) (3297612581 / 1000000000) (115983669 / 62500000) (1855774927 / 1000000000) (10107067 / 200000000000) (50551121 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0302 :
    ∀ t ∈ Set.Icc ((1551 / 64000) : ℝ) (97 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((131207821169 / 125000000000) : ℝ) ≤ Real.exp (2 * (1551 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1551 / 64000)) (131207821169 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((97 / 4000) : ℝ)) ≤ (1049695371821 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (97 / 4000)) (1049695371821 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((11598591 / 6250000) : ℝ) ≤ Real.exp (3 * (329761153 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (329761153 / 100000000) / 16) (11598591 / 6250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3297715633 / 1000000000) : ℝ) / 16) ≤ (371162157 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3297715633 / 1000000000) / 16) (371162157 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1551 / 64000) : ℝ) (97 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (329761153 / 100000000) (3297715633 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1551 / 64000) (97 / 4000) (131207821169 / 125000000000) (1049695371821 / 1000000000000) (329761153 / 100000000) (3297715633 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1551 / 64000) (97 / 4000) (329761153 / 100000000) (3297715633 / 1000000000) (25259857 / 500000000000) (6316937 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (329761153 / 100000000) (3297715633 / 1000000000) (11598591 / 6250000) (371162157 / 200000000) (25259857 / 500000000000) (6316937 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0303 :
    ∀ t ∈ Set.Icc ((97 / 4000) : ℝ) (1553 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((52484768591 / 50000000000) : ℝ) ≤ Real.exp (2 * (97 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (97 / 4000)) (52484768591 / 50000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1553 / 64000) : ℝ)) ≤ (524864087657 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1553 / 64000)) (524864087657 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((927905209 / 500000000) : ℝ) ≤ Real.exp (3 * (1648857291 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1648857291 / 500000000) / 16) (927905209 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((51528417 / 15625000) : ℝ) / 16) ≤ (371169329 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (51528417 / 15625000) / 16) (371169329 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((97 / 4000) : ℝ) (1553 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1648857291 / 500000000) (51528417 / 15625000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (97 / 4000) (1553 / 64000) (52484768591 / 50000000000) (524864087657 / 500000000000) (1648857291 / 500000000) (51528417 / 15625000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (97 / 4000) (1553 / 64000) (1648857291 / 500000000) (51528417 / 15625000) (25252049 / 500000000000) (404159 / 8000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1648857291 / 500000000) (51528417 / 15625000) (927905209 / 500000000) (371169329 / 200000000) (25252049 / 500000000000) (404159 / 8000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0304 :
    ∀ t ∈ Set.Icc ((1553 / 64000) : ℝ) (777 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1049728175313 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1553 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1553 / 64000)) (1049728175313 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((777 / 32000) : ℝ)) ≤ (131220122479 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (777 / 32000)) (131220122479 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((927923139 / 500000000) : ℝ) ≤ Real.exp (3 * (3297817637 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3297817637 / 1000000000) / 16) (927923139 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1648960873 / 500000000) : ℝ) / 16) ≤ (927941253 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1648960873 / 500000000) / 16) (927941253 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1553 / 64000) : ℝ) (777 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3297817637 / 1000000000) (1648960873 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1553 / 64000) (777 / 32000) (1049728175313 / 1000000000000) (131220122479 / 125000000000) (3297817637 / 1000000000) (1648960873 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1553 / 64000) (777 / 32000) (3297817637 / 1000000000) (1648960873 / 500000000) (25244243 / 500000000000) (50504259 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3297817637 / 1000000000) (1648960873 / 500000000) (927923139 / 500000000) (927941253 / 500000000) (25244243 / 500000000000) (50504259 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0305 :
    ∀ t ∈ Set.Icc ((777 / 32000) : ℝ) (311 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1049760979831 / 1000000000000) : ℝ) ≤ Real.exp (2 * (777 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (777 / 32000)) (1049760979831 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((311 / 12800) : ℝ)) ≤ (8398350283 / 8000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (311 / 12800)) (8398350283 / 8000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((92794107 / 50000000) : ℝ) ≤ Real.exp (3 * (412240087 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (412240087 / 125000000) / 16) (92794107 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((412253101 / 125000000) : ℝ) / 16) ≤ (185591837 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (412253101 / 125000000) / 16) (185591837 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((777 / 32000) : ℝ) (311 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (412240087 / 125000000) (412253101 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (777 / 32000) (311 / 12800) (1049760979831 / 1000000000000) (8398350283 / 8000000000) (412240087 / 125000000) (412253101 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (777 / 32000) (311 / 12800) (412240087 / 125000000) (412253101 / 125000000) (25236439 / 500000000000) (25244323 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (412240087 / 125000000) (412253101 / 125000000) (92794107 / 50000000) (185591837 / 100000000) (25236439 / 500000000000) (25244323 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0306 :
    ∀ t ∈ Set.Icc ((311 / 12800) : ℝ) (389 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((524896892687 / 500000000000) : ℝ) ≤ Real.exp (2 * (311 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (311 / 12800)) (524896892687 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((389 / 16000) : ℝ)) ≤ (1049826591943 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (389 / 16000)) (1049826591943 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1855918003 / 1000000000) : ℝ) ≤ Real.exp (3 * (3298023757 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3298023757 / 1000000000) / 16) (1855918003 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3298127873 / 1000000000) : ℝ) / 16) ≤ (371190847 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3298127873 / 1000000000) / 16) (371190847 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((311 / 12800) : ℝ) (389 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3298023757 / 1000000000) (3298127873 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (311 / 12800) (389 / 16000) (524896892687 / 500000000000) (1049826591943 / 1000000000000) (3298023757 / 1000000000) (3298127873 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (311 / 12800) (389 / 16000) (3298023757 / 1000000000) (3298127873 / 1000000000) (2018291 / 40000000000) (50473039 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3298023757 / 1000000000) (3298127873 / 1000000000) (1855918003 / 1000000000) (371190847 / 200000000) (2018291 / 40000000000) (50473039 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0307 :
    ∀ t ∈ Set.Icc ((389 / 16000) : ℝ) (1557 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((524913295971 / 500000000000) : ℝ) ≤ Real.exp (2 * (389 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (389 / 16000)) (524913295971 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1557 / 64000) : ℝ)) ≤ (1049859399537 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1557 / 64000)) (1049859399537 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1855953869 / 1000000000) : ℝ) ≤ Real.exp (3 * (1649063411 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1649063411 / 500000000) / 16) (1855953869 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3298230941 / 1000000000) : ℝ) / 16) ≤ (1855990103 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3298230941 / 1000000000) / 16) (1855990103 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((389 / 16000) : ℝ) (1557 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1649063411 / 500000000) (3298230941 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (389 / 16000) (1557 / 64000) (524913295971 / 500000000000) (1049859399537 / 1000000000000) (1649063411 / 500000000) (3298230941 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (389 / 16000) (1557 / 64000) (1649063411 / 500000000) (3298230941 / 1000000000) (2017667 / 40000000000) (10091487 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1649063411 / 500000000) (3298230941 / 1000000000) (1855953869 / 1000000000) (1855990103 / 1000000000) (2017667 / 40000000000) (10091487 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0308 :
    ∀ t ∈ Set.Icc ((1557 / 64000) : ℝ) (779 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((65616212471 / 62500000000) : ℝ) ≤ Real.exp (2 * (1557 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1557 / 64000)) (65616212471 / 62500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((779 / 32000) : ℝ)) ≤ (262473052039 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (779 / 32000)) (262473052039 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((231998717 / 125000000) : ℝ) ≤ Real.exp (3 * (329822989 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (329822989 / 100000000) / 16) (231998717 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((824583503 / 250000000) : ℝ) / 16) ≤ (1856025971 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (824583503 / 250000000) / 16) (1856025971 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1557 / 64000) : ℝ) (779 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (329822989 / 100000000) (824583503 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1557 / 64000) (779 / 32000) (65616212471 / 62500000000) (262473052039 / 250000000000) (329822989 / 100000000) (824583503 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1557 / 64000) (779 / 32000) (329822989 / 100000000) (824583503 / 250000000) (50426081 / 1000000000000) (12610459 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (329822989 / 100000000) (824583503 / 250000000) (231998717 / 125000000) (1856025971 / 1000000000) (50426081 / 1000000000000) (12610459 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0309 :
    ∀ t ∈ Set.Icc ((779 / 32000) : ℝ) (1559 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((209978441631 / 200000000000) : ℝ) ≤ Real.exp (2 * (779 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (779 / 32000)) (209978441631 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1559 / 64000) : ℝ)) ≤ (5249625089 / 5000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1559 / 64000)) (5249625089 / 5000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((371205121 / 200000000) : ℝ) ≤ Real.exp (3 * (1649166481 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1649166481 / 500000000) / 16) (371205121 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3298437087 / 1000000000) : ℝ) / 16) ≤ (928030921 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3298437087 / 1000000000) / 16) (928030921 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((779 / 32000) : ℝ) (1559 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1649166481 / 500000000) (3298437087 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (779 / 32000) (1559 / 64000) (209978441631 / 200000000000) (5249625089 / 5000000000) (1649166481 / 500000000) (3298437087 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (779 / 32000) (1559 / 64000) (1649166481 / 500000000) (3298437087 / 1000000000) (5041049 / 100000000000) (50426241 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1649166481 / 500000000) (3298437087 / 1000000000) (371205121 / 200000000) (928030921 / 500000000) (5041049 / 100000000000) (50426241 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0310 :
    ∀ t ∈ Set.Icc ((1559 / 64000) : ℝ) (39 / 1600), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1049925017799 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1559 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1559 / 64000)) (1049925017799 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((39 / 1600) : ℝ)) ≤ (1049957828469 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (39 / 1600)) (1049957828469 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((464015369 / 250000000) : ℝ) ≤ Real.exp (3 * (824609009 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (824609009 / 250000000) / 16) (464015369 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((659708033 / 200000000) : ℝ) / 16) ≤ (371219543 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (659708033 / 200000000) / 16) (371219543 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1559 / 64000) : ℝ) (39 / 1600),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (824609009 / 250000000) (659708033 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1559 / 64000) (39 / 1600) (1049925017799 / 1000000000000) (1049957828469 / 1000000000000) (824609009 / 250000000) (659708033 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1559 / 64000) (39 / 1600) (824609009 / 250000000) (659708033 / 200000000) (6299363 / 125000000000) (1008213 / 20000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (824609009 / 250000000) (659708033 / 200000000) (464015369 / 250000000) (371219543 / 200000000) (6299363 / 125000000000) (1008213 / 20000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0311 :
    ∀ t ∈ Set.Icc ((39 / 1600) : ℝ) (1561 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((262489457117 / 250000000000) : ℝ) ≤ Real.exp (2 * (39 / 1600)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (39 / 1600)) (262489457117 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1561 / 64000) : ℝ)) ≤ (262497660041 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1561 / 64000)) (262497660041 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((464024337 / 250000000) : ℝ) ≤ Real.exp (3 * (1649269557 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1649269557 / 500000000) / 16) (464024337 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1649321623 / 500000000) : ℝ) / 16) ≤ (185613359 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1649321623 / 500000000) / 16) (185613359 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((39 / 1600) : ℝ) (1561 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1649269557 / 500000000) (1649321623 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (39 / 1600) (1561 / 64000) (262489457117 / 250000000000) (262497660041 / 250000000000) (1649269557 / 500000000) (1649321623 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (39 / 1600) (1561 / 64000) (1649269557 / 500000000) (1649321623 / 500000000) (50379321 / 1000000000000) (6299383 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1649269557 / 500000000) (1649321623 / 500000000) (464024337 / 250000000) (185613359 / 100000000) (50379321 / 1000000000000) (6299383 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0312 :
    ∀ t ∈ Set.Icc ((1561 / 64000) : ℝ) (781 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1049990640163 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1561 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1561 / 64000)) (1049990640163 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((781 / 32000) : ℝ)) ≤ (210004690577 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (781 / 32000)) (210004690577 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1856133223 / 1000000000) : ℝ) ≤ Real.exp (3 * (659728439 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (659728439 / 200000000) / 16) (1856133223 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((329874633 / 100000000) : ℝ) / 16) ≤ (928084733 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (329874633 / 100000000) / 16) (928084733 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1561 / 64000) : ℝ) (781 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (659728439 / 200000000) (329874633 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1561 / 64000) (781 / 32000) (1049990640163 / 1000000000000) (210004690577 / 200000000000) (659728439 / 200000000) (329874633 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1561 / 64000) (781 / 32000) (659728439 / 200000000) (329874633 / 100000000) (1573867 / 31250000000) (25189741 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (659728439 / 200000000) (329874633 / 100000000) (1856133223 / 1000000000) (928084733 / 500000000) (1573867 / 31250000000) (25189741 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0313 :
    ∀ t ∈ Set.Icc ((781 / 32000) : ℝ) (1563 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((262505863221 / 250000000000) : ℝ) ≤ Real.exp (2 * (781 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (781 / 32000)) (262505863221 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1563 / 64000) : ℝ)) ≤ (105005626663 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1563 / 64000)) (105005626663 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1856169099 / 1000000000) : ℝ) ≤ Real.exp (3 * (3298745279 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3298745279 / 1000000000) / 16) (1856169099 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3298849417 / 1000000000) : ℝ) / 16) ≤ (58006417 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3298849417 / 1000000000) / 16) (58006417 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((781 / 32000) : ℝ) (1563 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3298745279 / 1000000000) (3298849417 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (781 / 32000) (1563 / 64000) (262505863221 / 250000000000) (105005626663 / 100000000000) (3298745279 / 1000000000) (3298849417 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (781 / 32000) (1563 / 64000) (3298745279 / 1000000000) (3298849417 / 1000000000) (50348171 / 1000000000000) (98367 / 1953125000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3298745279 / 1000000000) (3298849417 / 1000000000) (1856169099 / 1000000000) (58006417 / 31250000) (50348171 / 1000000000000) (98367 / 1953125000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0314 :
    ∀ t ∈ Set.Icc ((1563 / 64000) : ℝ) (391 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1050056266629 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1563 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1563 / 64000)) (1050056266629 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((391 / 16000) : ℝ)) ≤ (1050089081401 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (391 / 16000)) (1050089081401 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1856204977 / 1000000000) : ℝ) ≤ Real.exp (3 * (1649424183 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1649424183 / 500000000) / 16) (1856204977 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((824738127 / 250000000) : ℝ) / 16) ≤ (232030153 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (824738127 / 250000000) / 16) (232030153 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1563 / 64000) : ℝ) (391 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1649424183 / 500000000) (824738127 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1563 / 64000) (391 / 16000) (1050056266629 / 1000000000000) (1050089081401 / 1000000000000) (1649424183 / 500000000) (824738127 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1563 / 64000) (391 / 16000) (1649424183 / 500000000) (824738127 / 250000000) (25166301 / 500000000000) (50348331 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1649424183 / 500000000) (824738127 / 250000000) (1856204977 / 1000000000) (232030153 / 125000000) (25166301 / 500000000000) (50348331 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0315 :
    ∀ t ∈ Set.Icc ((391 / 16000) : ℝ) (313 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((5250445407 / 5000000000) : ℝ) ≤ Real.exp (2 * (391 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (391 / 16000)) (5250445407 / 5000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((313 / 12800) : ℝ)) ≤ (525060948599 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (313 / 12800)) (525060948599 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1856240857 / 1000000000) : ℝ) ≤ Real.exp (3 * (3298951457 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3298951457 / 1000000000) / 16) (1856240857 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1649527801 / 500000000) : ℝ) / 16) ≤ (371255421 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1649527801 / 500000000) / 16) (371255421 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((391 / 16000) : ℝ) (313 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3298951457 / 1000000000) (1649527801 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (391 / 16000) (313 / 12800) (5250445407 / 5000000000) (525060948599 / 500000000000) (3298951457 / 1000000000) (1649527801 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (391 / 16000) (313 / 12800) (3298951457 / 1000000000) (1649527801 / 500000000) (25158519 / 500000000000) (25166381 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3298951457 / 1000000000) (1649527801 / 500000000) (1856240857 / 1000000000) (371255421 / 200000000) (25158519 / 500000000000) (25166381 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0316 :
    ∀ t ∈ Set.Icc ((313 / 12800) : ℝ) (783 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1050121897197 / 1000000000000) : ℝ) ≤ Real.exp (2 * (313 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (313 / 12800)) (1050121897197 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((783 / 32000) : ℝ)) ≤ (52507735701 / 50000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (783 / 32000)) (52507735701 / 50000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((928138369 / 500000000) : ℝ) ≤ Real.exp (3 * (3299054551 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3299054551 / 1000000000) / 16) (928138369 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3299158699 / 1000000000) : ℝ) / 16) ≤ (1856312989 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3299158699 / 1000000000) / 16) (1856312989 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((313 / 12800) : ℝ) (783 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3299054551 / 1000000000) (3299158699 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (313 / 12800) (783 / 32000) (1050121897197 / 1000000000000) (52507735701 / 50000000000) (3299054551 / 1000000000) (3299158699 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (313 / 12800) (783 / 32000) (3299054551 / 1000000000) (3299158699 / 1000000000) (50301477 / 1000000000000) (25158599 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3299054551 / 1000000000) (3299158699 / 1000000000) (928138369 / 500000000) (1856312989 / 1000000000) (50301477 / 1000000000000) (25158599 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0317 :
    ∀ t ∈ Set.Icc ((783 / 32000) : ℝ) (1567 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1050154714019 / 1000000000000) : ℝ) ≤ Real.exp (2 * (783 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (783 / 32000)) (1050154714019 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1567 / 64000) : ℝ)) ≤ (1050187531867 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1567 / 64000)) (1050187531867 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((928156311 / 500000000) : ℝ) ≤ Real.exp (3 * (206197353 / 62500000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (206197353 / 62500000) / 16) (928156311 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3299261799 / 1000000000) : ℝ) / 16) ≤ (928174437 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3299261799 / 1000000000) / 16) (928174437 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((783 / 32000) : ℝ) (1567 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (206197353 / 62500000) (3299261799 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (783 / 32000) (1567 / 64000) (1050154714019 / 1000000000000) (1050187531867 / 1000000000000) (206197353 / 62500000) (3299261799 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (783 / 32000) (1567 / 64000) (206197353 / 62500000) (3299261799 / 1000000000) (50285921 / 1000000000000) (50301637 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (206197353 / 62500000) (3299261799 / 1000000000) (928156311 / 500000000) (928174437 / 500000000) (50285921 / 1000000000000) (50301637 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0318 :
    ∀ t ∈ Set.Icc ((1567 / 64000) : ℝ) (49 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((525093765933 / 500000000000) : ℝ) ≤ Real.exp (2 * (1567 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1567 / 64000)) (525093765933 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((49 / 2000) : ℝ)) ≤ (1050220350741 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (49 / 2000)) (1050220350741 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1856348507 / 1000000000) : ℝ) ≤ Real.exp (3 * (824815187 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (824815187 / 250000000) / 16) (1856348507 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3299364903 / 1000000000) : ℝ) / 16) ≤ (1856384761 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3299364903 / 1000000000) / 16) (1856384761 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1567 / 64000) : ℝ) (49 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (824815187 / 250000000) (3299364903 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1567 / 64000) (49 / 2000) (525093765933 / 500000000000) (1050220350741 / 1000000000000) (824815187 / 250000000) (3299364903 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1567 / 64000) (49 / 2000) (824815187 / 250000000) (3299364903 / 1000000000) (5027037 / 100000000000) (25143041 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (824815187 / 250000000) (3299364903 / 1000000000) (1856348507 / 1000000000) (1856384761 / 1000000000) (5027037 / 100000000000) (25143041 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0319 :
    ∀ t ∈ Set.Icc ((49 / 2000) : ℝ) (1569 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((52511017537 / 50000000000) : ℝ) ≤ Real.exp (2 * (49 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (49 / 2000)) (52511017537 / 50000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1569 / 64000) : ℝ)) ≤ (1050253170639 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1569 / 64000)) (1050253170639 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((928192197 / 500000000) : ℝ) ≤ Real.exp (3 * (824840963 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (824840963 / 250000000) / 16) (928192197 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((329946801 / 100000000) : ℝ) / 16) ≤ (37128413 / 20000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (329946801 / 100000000) / 16) (37128413 / 20000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((49 / 2000) : ℝ) (1569 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (824840963 / 250000000) (329946801 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (49 / 2000) (1569 / 64000) (52511017537 / 50000000000) (1050253170639 / 1000000000000) (824840963 / 250000000) (329946801 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (49 / 2000) (1569 / 64000) (824840963 / 250000000) (329946801 / 100000000) (50254823 / 1000000000000) (5027053 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (824840963 / 250000000) (329946801 / 100000000) (928192197 / 500000000) (37128413 / 20000000) (50254823 / 1000000000000) (5027053 / 100000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch015 :
    ∀ t ∈ Set.Icc ((1549 / 64000) : ℝ) (1569 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0300
      hpThetaDensityTwoTermCompact_cell0301)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0302
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0303
      hpThetaDensityTwoTermCompact_cell0304)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0305
      hpThetaDensityTwoTermCompact_cell0306)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0307
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0308
      hpThetaDensityTwoTermCompact_cell0309))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0310
      hpThetaDensityTwoTermCompact_cell0311)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0312
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0313
      hpThetaDensityTwoTermCompact_cell0314)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0315
      hpThetaDensityTwoTermCompact_cell0316)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0317
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0318
      hpThetaDensityTwoTermCompact_cell0319)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch015
end HodgeProofHP
