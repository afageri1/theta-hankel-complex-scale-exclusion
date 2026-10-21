/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0200 :
    ∀ t ∈ Set.Icc ((1449 / 64000) : ℝ) (29 / 1280), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1046322096619 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1449 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1449 / 64000)) (1046322096619 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((29 / 1280) : ℝ)) ≤ (130794349337 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (29 / 1280)) (130794349337 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((926063271 / 500000000) : ℝ) ≤ Real.exp (3 * (410889641 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (410889641 / 125000000) / 16) (926063271 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3287220899 / 1000000000) : ℝ) / 16) ≤ (1852162581 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3287220899 / 1000000000) / 16) (1852162581 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1449 / 64000) : ℝ) (29 / 1280),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (410889641 / 125000000) (3287220899 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1449 / 64000) (29 / 1280) (1046322096619 / 1000000000000) (130794349337 / 125000000000) (410889641 / 125000000) (3287220899 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1449 / 64000) (29 / 1280) (410889641 / 125000000) (3287220899 / 1000000000) (52135591 / 1000000000000) (26075913 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (410889641 / 125000000) (3287220899 / 1000000000) (926063271 / 500000000) (1852162581 / 1000000000) (52135591 / 1000000000000) (26075913 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0201 :
    ∀ t ∈ Set.Icc ((29 / 1280) : ℝ) (1451 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((209270958939 / 200000000000) : ℝ) ≤ Real.exp (2 * (29 / 1280)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (29 / 1280)) (209270958939 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1451 / 64000) : ℝ)) ≤ (209277498759 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1451 / 64000)) (209277498759 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((231520277 / 125000000) : ℝ) ≤ Real.exp (3 * (821804963 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (821804963 / 250000000) / 16) (231520277 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1643661813 / 500000000) : ℝ) / 16) ≤ (115762391 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1643661813 / 500000000) / 16) (115762391 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((29 / 1280) : ℝ) (1451 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (821804963 / 250000000) (1643661813 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (29 / 1280) (1451 / 64000) (209270958939 / 200000000000) (209277498759 / 200000000000) (821804963 / 250000000) (1643661813 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (29 / 1280) (1451 / 64000) (821804963 / 250000000) (1643661813 / 500000000) (26059763 / 500000000000) (13033939 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (821804963 / 250000000) (1643661813 / 500000000) (231520277 / 125000000) (115762391 / 62500000) (26059763 / 500000000000) (13033939 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0202 :
    ∀ t ∈ Set.Icc ((1451 / 64000) : ℝ) (363 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((523193746897 / 500000000000) : ℝ) ≤ Real.exp (2 * (1451 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1451 / 64000)) (523193746897 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((363 / 16000) : ℝ)) ≤ (209284038783 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (363 / 16000)) (209284038783 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1852197891 / 1000000000) : ℝ) ≤ Real.exp (3 * (3287322579 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3287322579 / 1000000000) / 16) (1852197891 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3287426357 / 1000000000) : ℝ) / 16) ≤ (1852233933 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3287426357 / 1000000000) / 16) (1852233933 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1451 / 64000) : ℝ) (363 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3287322579 / 1000000000) (3287426357 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1451 / 64000) (363 / 16000) (523193746897 / 500000000000) (209284038783 / 200000000000) (3287322579 / 1000000000) (3287426357 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1451 / 64000) (363 / 16000) (3287322579 / 1000000000) (3287426357 / 1000000000) (26051733 / 500000000000) (13029923 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3287322579 / 1000000000) (3287426357 / 1000000000) (1852197891 / 1000000000) (1852233933 / 1000000000) (26051733 / 500000000000) (13029923 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0203 :
    ∀ t ∈ Set.Icc ((363 / 16000) : ℝ) (1453 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((523210096957 / 500000000000) : ℝ) ≤ Real.exp (2 * (363 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (363 / 16000)) (523210096957 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1453 / 64000) : ℝ)) ≤ (1046452895057 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1453 / 64000)) (1046452895057 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((57882299 / 31250000) : ℝ) ≤ Real.exp (3 * (3287425309 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3287425309 / 1000000000) / 16) (57882299 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((328752909 / 100000000) : ℝ) / 16) ≤ (463067403 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (328752909 / 100000000) / 16) (463067403 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((363 / 16000) : ℝ) (1453 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3287425309 / 1000000000) (328752909 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (363 / 16000) (1453 / 64000) (523210096957 / 500000000000) (1046452895057 / 1000000000000) (3287425309 / 1000000000) (328752909 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (363 / 16000) (1453 / 64000) (3287425309 / 1000000000) (328752909 / 100000000) (5208741 / 100000000000) (3256477 / 62500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3287425309 / 1000000000) (328752909 / 100000000) (57882299 / 31250000) (463067403 / 250000000) (5208741 / 100000000000) (3256477 / 62500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0204 :
    ∀ t ∈ Set.Icc ((1453 / 64000) : ℝ) (727 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((65403305941 / 62500000000) : ℝ) ≤ Real.exp (2 * (1453 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1453 / 64000)) (65403305941 / 62500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((727 / 32000) : ℝ)) ≤ (1046485597221 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (727 / 32000)) (1046485597221 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((28941707 / 15625000) : ℝ) ≤ Real.exp (3 * (3287528043 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3287528043 / 1000000000) / 16) (28941707 / 15625000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3287631827 / 1000000000) : ℝ) / 16) ≤ (1852305293 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3287631827 / 1000000000) / 16) (1852305293 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1453 / 64000) : ℝ) (727 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3287528043 / 1000000000) (3287631827 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1453 / 64000) (727 / 32000) (65403305941 / 62500000000) (1046485597221 / 1000000000000) (3287528043 / 1000000000) (3287631827 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1453 / 64000) (727 / 32000) (3287528043 / 1000000000) (3287631827 / 1000000000) (52071359 / 1000000000000) (2083503 / 40000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3287528043 / 1000000000) (3287631827 / 1000000000) (28941707 / 15625000) (1852305293 / 1000000000) (52071359 / 1000000000000) (2083503 / 40000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0205 :
    ∀ t ∈ Set.Icc ((727 / 32000) : ℝ) (291 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((52324279861 / 50000000000) : ℝ) ≤ Real.exp (2 * (727 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (727 / 32000)) (52324279861 / 50000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((291 / 12800) : ℝ)) ≤ (1046518300407 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (291 / 12800)) (1046518300407 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1852304929 / 1000000000) : ℝ) ≤ Real.exp (3 * (164381539 / 50000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (164381539 / 50000000) / 16) (1852304929 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3287734567 / 1000000000) : ℝ) / 16) ≤ (115771311 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3287734567 / 1000000000) / 16) (115771311 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((727 / 32000) : ℝ) (291 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (164381539 / 50000000) (3287734567 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (727 / 32000) (291 / 12800) (52324279861 / 50000000000) (1046518300407 / 1000000000000) (164381539 / 50000000) (3287734567 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (727 / 32000) (291 / 12800) (164381539 / 50000000) (3287734567 / 1000000000) (3253457 / 62500000000) (13017881 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (164381539 / 50000000) (3287734567 / 1000000000) (1852304929 / 1000000000) (115771311 / 62500000) (3253457 / 62500000000) (13017881 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0206 :
    ∀ t ∈ Set.Icc ((291 / 12800) : ℝ) (91 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((523259150203 / 500000000000) : ℝ) ≤ Real.exp (2 * (291 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (291 / 12800)) (523259150203 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((91 / 4000) : ℝ)) ≤ (523275502307 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (91 / 4000)) (523275502307 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1852340611 / 1000000000) : ℝ) ≤ Real.exp (3 * (41096669 / 12500000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (41096669 / 12500000) / 16) (1852340611 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3287837311 / 1000000000) : ℝ) / 16) ≤ (1852376661 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3287837311 / 1000000000) / 16) (1852376661 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((291 / 12800) : ℝ) (91 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (41096669 / 12500000) (3287837311 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (291 / 12800) (91 / 4000) (523259150203 / 500000000000) (523275502307 / 500000000000) (41096669 / 12500000) (3287837311 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (291 / 12800) (91 / 4000) (41096669 / 12500000) (3287837311 / 1000000000) (52039269 / 1000000000000) (52055477 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (41096669 / 12500000) (3287837311 / 1000000000) (1852340611 / 1000000000) (1852376661 / 1000000000) (52039269 / 1000000000000) (52055477 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0207 :
    ∀ t ∈ Set.Icc ((91 / 4000) : ℝ) (1457 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1046551004613 / 1000000000000) : ℝ) ≤ Real.exp (2 * (91 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (91 / 4000)) (1046551004613 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1457 / 64000) : ℝ)) ≤ (261645927461 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1457 / 64000)) (261645927461 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((231547037 / 125000000) : ℝ) ≤ Real.exp (3 * (3287836263 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3287836263 / 1000000000) / 16) (231547037 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3287940057 / 1000000000) : ℝ) / 16) ≤ (1852412347 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3287940057 / 1000000000) / 16) (1852412347 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((91 / 4000) : ℝ) (1457 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3287836263 / 1000000000) (3287940057 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (91 / 4000) (1457 / 64000) (1046551004613 / 1000000000000) (261645927461 / 250000000000) (3287836263 / 1000000000) (3287940057 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (91 / 4000) (1457 / 64000) (3287836263 / 1000000000) (3287940057 / 1000000000) (52023231 / 1000000000000) (26019717 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3287836263 / 1000000000) (3287940057 / 1000000000) (231547037 / 125000000) (1852412347 / 1000000000) (52023231 / 1000000000000) (26019717 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0208 :
    ∀ t ∈ Set.Icc ((1457 / 64000) : ℝ) (729 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1046583709843 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1457 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1457 / 64000)) (1046583709843 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((729 / 32000) : ℝ)) ≤ (32706763003 / 31250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (729 / 32000)) (32706763003 / 31250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((926205991 / 500000000) : ℝ) ≤ Real.exp (3 * (328793901 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (328793901 / 100000000) / 16) (926205991 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3288042807 / 1000000000) : ℝ) / 16) ≤ (370489607 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3288042807 / 1000000000) / 16) (370489607 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1457 / 64000) : ℝ) (729 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (328793901 / 100000000) (3288042807 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1457 / 64000) (729 / 32000) (1046583709843 / 1000000000000) (32706763003 / 31250000000) (328793901 / 100000000) (3288042807 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1457 / 64000) (729 / 32000) (328793901 / 100000000) (3288042807 / 1000000000) (26003599 / 500000000000) (13005849 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (328793901 / 100000000) (3288042807 / 1000000000) (926205991 / 500000000) (370489607 / 200000000) (26003599 / 500000000000) (13005849 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0209 :
    ∀ t ∈ Set.Icc ((729 / 32000) : ℝ) (1459 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((209323283219 / 200000000000) : ℝ) ≤ Real.exp (2 * (729 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (729 / 32000)) (209323283219 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1459 / 64000) : ℝ)) ≤ (104664912337 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1459 / 64000)) (104664912337 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((185244767 / 100000000) : ℝ) ≤ Real.exp (3 * (3288041759 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3288041759 / 1000000000) / 16) (185244767 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((82203639 / 25000000) : ℝ) / 16) ≤ (74099349 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (82203639 / 25000000) / 16) (74099349 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((729 / 32000) : ℝ) (1459 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3288041759 / 1000000000) (82203639 / 25000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (729 / 32000) (1459 / 64000) (209323283219 / 200000000000) (104664912337 / 100000000000) (3288041759 / 1000000000) (82203639 / 25000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (729 / 32000) (1459 / 64000) (3288041759 / 1000000000) (82203639 / 25000000) (406181 / 7812500000) (52007363 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3288041759 / 1000000000) (82203639 / 25000000) (185244767 / 100000000) (74099349 / 40000000) (406181 / 7812500000) (52007363 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0210 :
    ∀ t ∈ Set.Icc ((1459 / 64000) : ℝ) (73 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1046649123369 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1459 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1459 / 64000)) (1046649123369 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((73 / 3200) : ℝ)) ≤ (1046681831667 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (73 / 3200)) (1046681831667 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((11578021 / 6250000) : ℝ) ≤ Real.exp (3 * (25688629 / 7812500) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (25688629 / 7812500) / 16) (11578021 / 6250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((822062079 / 250000000) : ℝ) / 16) ≤ (1852519417 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (822062079 / 250000000) / 16) (1852519417 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1459 / 64000) : ℝ) (73 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (25688629 / 7812500) (822062079 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1459 / 64000) (73 / 3200) (1046649123369 / 1000000000000) (1046681831667 / 1000000000000) (25688629 / 7812500) (822062079 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1459 / 64000) (73 / 3200) (25688629 / 7812500) (822062079 / 250000000) (51975143 / 1000000000000) (51991333 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (25688629 / 7812500) (822062079 / 250000000) (11578021 / 6250000) (1852519417 / 1000000000) (51975143 / 1000000000000) (51991333 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0211 :
    ∀ t ∈ Set.Icc ((73 / 3200) : ℝ) (1461 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((523340915833 / 500000000000) : ℝ) ≤ Real.exp (2 * (73 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (73 / 3200)) (523340915833 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1461 / 64000) : ℝ)) ≤ (209342908197 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1461 / 64000)) (209342908197 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((463129763 / 250000000) : ℝ) ≤ Real.exp (3 * (822061817 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (822061817 / 250000000) / 16) (463129763 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((131534043 / 40000000) : ℝ) / 16) ≤ (185255511 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (131534043 / 40000000) / 16) (185255511 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((73 / 3200) : ℝ) (1461 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (822061817 / 250000000) (131534043 / 40000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (73 / 3200) (1461 / 64000) (523340915833 / 500000000000) (209342908197 / 200000000000) (822061817 / 250000000) (131534043 / 40000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (73 / 3200) (1461 / 64000) (822061817 / 250000000) (131534043 / 40000000) (51959123 / 1000000000000) (12993827 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (822061817 / 250000000) (131534043 / 40000000) (463129763 / 250000000) (185255511 / 100000000) (51959123 / 1000000000000) (12993827 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0212 :
    ∀ t ∈ Set.Icc ((1461 / 64000) : ℝ) (731 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((130839317623 / 125000000000) : ℝ) ≤ Real.exp (2 * (1461 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1461 / 64000)) (130839317623 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((731 / 32000) : ℝ)) ≤ (41869890053 / 40000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (731 / 32000)) (41869890053 / 40000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((370510949 / 200000000) : ℝ) ≤ Real.exp (3 * (822087507 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (822087507 / 250000000) / 16) (370510949 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1644226919 / 500000000) : ℝ) / 16) ≤ (926295403 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1644226919 / 500000000) / 16) (926295403 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1461 / 64000) : ℝ) (731 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (822087507 / 250000000) (1644226919 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1461 / 64000) (731 / 32000) (130839317623 / 125000000000) (41869890053 / 40000000000) (822087507 / 250000000) (1644226919 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1461 / 64000) (731 / 32000) (822087507 / 250000000) (1644226919 / 500000000) (51943107 / 1000000000000) (6494911 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (822087507 / 250000000) (1644226919 / 500000000) (370510949 / 200000000) (926295403 / 500000000) (51943107 / 1000000000000) (6494911 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0213 :
    ∀ t ∈ Set.Icc ((731 / 32000) : ℝ) (1463 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((261686812831 / 250000000000) : ℝ) ≤ Real.exp (2 * (731 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (731 / 32000)) (261686812831 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1463 / 64000) : ℝ)) ≤ (16355936917 / 15625000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1463 / 64000)) (16355936917 / 15625000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1852590441 / 1000000000) : ℝ) ≤ Real.exp (3 * (328845279 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (328845279 / 100000000) / 16) (1852590441 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((822139151 / 250000000) : ℝ) / 16) ≤ (1852626503 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (822139151 / 250000000) / 16) (1852626503 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((731 / 32000) : ℝ) (1463 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (328845279 / 100000000) (822139151 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (731 / 32000) (1463 / 64000) (261686812831 / 250000000000) (16355936917 / 15625000000) (328845279 / 100000000) (822139151 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (731 / 32000) (1463 / 64000) (328845279 / 100000000) (822139151 / 250000000) (6490887 / 125000000000) (6492909 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (328845279 / 100000000) (822139151 / 250000000) (1852590441 / 1000000000) (1852626503 / 1000000000) (6490887 / 125000000000) (6492909 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0214 :
    ∀ t ∈ Set.Icc ((1463 / 64000) : ℝ) (183 / 8000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1046779962687 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1463 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1463 / 64000)) (1046779962687 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((183 / 8000) : ℝ)) ≤ (1046812675073 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (183 / 8000)) (1046812675073 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((926313069 / 500000000) : ℝ) ≤ Real.exp (3 * (822138889 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (822138889 / 250000000) / 16) (926313069 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3288659373 / 1000000000) : ℝ) / 16) ≤ (926331101 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3288659373 / 1000000000) / 16) (926331101 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1463 / 64000) : ℝ) (183 / 8000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (822138889 / 250000000) (3288659373 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1463 / 64000) (183 / 8000) (1046779962687 / 1000000000000) (1046812675073 / 1000000000000) (822138889 / 250000000) (3288659373 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1463 / 64000) (183 / 8000) (822138889 / 250000000) (3288659373 / 1000000000) (51911089 / 1000000000000) (2596363 / 50000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (822138889 / 250000000) (3288659373 / 1000000000) (926313069 / 500000000) (926331101 / 500000000) (51911089 / 1000000000000) (2596363 / 50000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0215 :
    ∀ t ∈ Set.Icc ((183 / 8000) : ℝ) (293 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1022278003 / 976562500) : ℝ) ≤ Real.exp (2 * (183 / 8000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (183 / 8000)) (1022278003 / 976562500) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((293 / 12800) : ℝ)) ≤ (3271391839 / 3125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (293 / 12800)) (3271391839 / 3125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1852661837 / 1000000000) : ℝ) ≤ Real.exp (3 * (131546333 / 40000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (131546333 / 40000000) / 16) (1852661837 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((657752429 / 200000000) : ℝ) / 16) ≤ (1852697903 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (657752429 / 200000000) / 16) (1852697903 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((183 / 8000) : ℝ) (293 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (131546333 / 40000000) (657752429 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (183 / 8000) (293 / 12800) (1022278003 / 976562500) (3271391839 / 3125000000) (131546333 / 40000000) (657752429 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (183 / 8000) (293 / 12800) (131546333 / 40000000) (657752429 / 200000000) (25947543 / 500000000000) (51911253 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (131546333 / 40000000) (657752429 / 200000000) (1852661837 / 1000000000) (1852697903 / 1000000000) (25947543 / 500000000000) (51911253 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0216 :
    ∀ t ∈ Set.Icc ((293 / 12800) : ℝ) (733 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1046845388479 / 1000000000000) : ℝ) ≤ Real.exp (2 * (293 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (293 / 12800)) (1046845388479 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((733 / 32000) : ℝ)) ≤ (104687810291 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (733 / 32000)) (104687810291 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1852697537 / 1000000000) : ℝ) ≤ Real.exp (3 * (3288761097 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3288761097 / 1000000000) / 16) (1852697537 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((82221623 / 25000000) : ℝ) / 16) ≤ (370546721 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (82221623 / 25000000) / 16) (370546721 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((293 / 12800) : ℝ) (733 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3288761097 / 1000000000) (82221623 / 25000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (293 / 12800) (733 / 32000) (1046845388479 / 1000000000000) (104687810291 / 100000000000) (3288761097 / 1000000000) (82221623 / 25000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (293 / 12800) (733 / 32000) (3288761097 / 1000000000) (82221623 / 25000000) (3242443 / 62500000000) (51895251 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3288761097 / 1000000000) (82221623 / 25000000) (1852697537 / 1000000000) (370546721 / 200000000) (3242443 / 62500000000) (51895251 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0217 :
    ∀ t ∈ Set.Icc ((733 / 32000) : ℝ) (1467 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1046878102909 / 1000000000000) : ℝ) ≤ Real.exp (2 * (733 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (733 / 32000)) (1046878102909 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1467 / 64000) : ℝ)) ≤ (523455409181 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1467 / 64000)) (523455409181 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((46318331 / 25000000) : ℝ) ≤ Real.exp (3 * (3288863873 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3288863873 / 1000000000) / 16) (46318331 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3288967699 / 1000000000) : ℝ) / 16) ≤ (1852769309 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3288967699 / 1000000000) / 16) (1852769309 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((733 / 32000) : ℝ) (1467 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3288863873 / 1000000000) (3288967699 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (733 / 32000) (1467 / 64000) (1046878102909 / 1000000000000) (523455409181 / 500000000000) (3288863873 / 1000000000) (3288967699 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (733 / 32000) (1467 / 64000) (3288863873 / 1000000000) (3288967699 / 1000000000) (10372619 / 200000000000) (51879253 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3288863873 / 1000000000) (3288967699 / 1000000000) (46318331 / 25000000) (1852769309 / 1000000000) (10372619 / 200000000000) (51879253 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0218 :
    ∀ t ∈ Set.Icc ((1467 / 64000) : ℝ) (367 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1046910818361 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1467 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1467 / 64000)) (1046910818361 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((367 / 16000) : ℝ)) ≤ (261735883709 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (367 / 16000)) (261735883709 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((115798059 / 62500000) : ℝ) ≤ Real.exp (3 * (3288966651 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3288966651 / 1000000000) / 16) (115798059 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3289070481 / 1000000000) : ℝ) / 16) ≤ (231600627 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3289070481 / 1000000000) / 16) (231600627 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1467 / 64000) : ℝ) (367 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3288966651 / 1000000000) (3289070481 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1467 / 64000) (367 / 16000) (1046910818361 / 1000000000000) (261735883709 / 250000000000) (3288966651 / 1000000000) (3289070481 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1467 / 64000) (367 / 16000) (3288966651 / 1000000000) (3289070481 / 1000000000) (10369421 / 200000000000) (51863259 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3288966651 / 1000000000) (3289070481 / 1000000000) (115798059 / 62500000) (231600627 / 125000000) (10369421 / 200000000000) (51863259 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0219 :
    ∀ t ∈ Set.Icc ((367 / 16000) : ℝ) (1469 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((209388706967 / 200000000000) : ℝ) ≤ Real.exp (2 * (367 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (367 / 16000)) (209388706967 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1469 / 64000) : ℝ)) ≤ (1046976252333 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1469 / 64000)) (1046976252333 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1852804651 / 1000000000) : ℝ) ≤ Real.exp (3 * (3289069433 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3289069433 / 1000000000) / 16) (1852804651 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1644586633 / 500000000) : ℝ) / 16) ≤ (463210181 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1644586633 / 500000000) / 16) (463210181 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((367 / 16000) : ℝ) (1469 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3289069433 / 1000000000) (1644586633 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (367 / 16000) (1469 / 64000) (209388706967 / 200000000000) (1046976252333 / 1000000000000) (3289069433 / 1000000000) (1644586633 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (367 / 16000) (1469 / 64000) (3289069433 / 1000000000) (1644586633 / 500000000) (647889 / 12500000000) (51847269 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3289069433 / 1000000000) (1644586633 / 500000000) (1852804651 / 1000000000) (463210181 / 250000000) (647889 / 12500000000) (51847269 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch010 :
    ∀ t ∈ Set.Icc ((1449 / 64000) : ℝ) (1469 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0200
      hpThetaDensityTwoTermCompact_cell0201)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0202
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0203
      hpThetaDensityTwoTermCompact_cell0204)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0205
      hpThetaDensityTwoTermCompact_cell0206)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0207
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0208
      hpThetaDensityTwoTermCompact_cell0209))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0210
      hpThetaDensityTwoTermCompact_cell0211)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0212
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0213
      hpThetaDensityTwoTermCompact_cell0214)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0215
      hpThetaDensityTwoTermCompact_cell0216)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0217
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0218
      hpThetaDensityTwoTermCompact_cell0219)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch010
end HodgeProofHP
