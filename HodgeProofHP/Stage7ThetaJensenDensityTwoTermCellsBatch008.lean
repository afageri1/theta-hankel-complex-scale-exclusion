/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0160 :
    ∀ t ∈ Set.Icc ((1409 / 64000) : ℝ) (141 / 6400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1045015011097 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1409 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1409 / 64000)) (1045015011097 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((141 / 6400) : ℝ)) ≤ (1045047668327 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (141 / 6400)) (1045047668327 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1850701071 / 1000000000) : ℝ) ≤ Real.exp (3 * (1641505399 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1641505399 / 500000000) / 16) (1850701071 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((82077861 / 25000000) : ℝ) / 16) ≤ (462684259 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (82077861 / 25000000) / 16) (462684259 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1409 / 64000) : ℝ) (141 / 6400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1641505399 / 500000000) (82077861 / 25000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1409 / 64000) (141 / 6400) (1045015011097 / 1000000000000) (1045047668327 / 1000000000000) (1641505399 / 500000000) (82077861 / 25000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1409 / 64000) (141 / 6400) (1641505399 / 500000000) (82077861 / 25000000) (26390921 / 500000000000) (52798257 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1641505399 / 500000000) (82077861 / 25000000) (1850701071 / 1000000000) (462684259 / 250000000) (26390921 / 500000000000) (52798257 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0161 :
    ∀ t ∈ Set.Icc ((141 / 6400) : ℝ) (1411 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((522523834163 / 500000000000) : ℝ) ≤ Real.exp (2 * (141 / 6400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (141 / 6400)) (522523834163 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1411 / 64000) : ℝ)) ≤ (1045080326577 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1411 / 64000)) (1045080326577 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((57835521 / 31250000) : ℝ) ≤ Real.exp (3 * (1641556697 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1641556697 / 500000000) / 16) (57835521 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3283217039 / 1000000000) : ℝ) / 16) ≤ (11567329 / 6250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3283217039 / 1000000000) / 16) (11567329 / 6250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((141 / 6400) : ℝ) (1411 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1641556697 / 500000000) (3283217039 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (141 / 6400) (1411 / 64000) (522523834163 / 500000000000) (1045080326577 / 1000000000000) (1641556697 / 500000000) (3283217039 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (141 / 6400) (1411 / 64000) (1641556697 / 500000000) (3283217039 / 1000000000) (26382799 / 500000000000) (52782009 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1641556697 / 500000000) (3283217039 / 1000000000) (57835521 / 31250000) (11567329 / 6250000) (26382799 / 500000000000) (52782009 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0162 :
    ∀ t ∈ Set.Icc ((1411 / 64000) : ℝ) (353 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((65317520411 / 62500000000) : ℝ) ≤ Real.exp (2 * (1411 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1411 / 64000)) (65317520411 / 62500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((353 / 16000) : ℝ)) ≤ (130639123231 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (353 / 16000)) (130639123231 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((462693069 / 250000000) : ℝ) ≤ Real.exp (3 * (3283215993 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3283215993 / 1000000000) / 16) (462693069 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3283319641 / 1000000000) : ℝ) / 16) ≤ (370161649 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3283319641 / 1000000000) / 16) (370161649 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1411 / 64000) : ℝ) (353 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3283215993 / 1000000000) (3283319641 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1411 / 64000) (353 / 16000) (65317520411 / 62500000000) (130639123231 / 125000000000) (3283215993 / 1000000000) (3283319641 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1411 / 64000) (353 / 16000) (3283215993 / 1000000000) (3283319641 / 1000000000) (52749359 / 1000000000000) (10553153 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3283215993 / 1000000000) (3283319641 / 1000000000) (462693069 / 250000000) (370161649 / 200000000) (52749359 / 1000000000000) (10553153 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0163 :
    ∀ t ∈ Set.Icc ((353 / 16000) : ℝ) (1413 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1045112985847 / 1000000000000) : ℝ) ≤ Real.exp (2 * (353 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (353 / 16000)) (1045112985847 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1413 / 64000) : ℝ)) ≤ (1045145646139 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1413 / 64000)) (1045145646139 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1850807881 / 1000000000) : ℝ) ≤ Real.exp (3 * (656663719 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (656663719 / 200000000) / 16) (1850807881 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1641711123 / 500000000) : ℝ) / 16) ≤ (462710963 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1641711123 / 500000000) / 16) (462710963 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((353 / 16000) : ℝ) (1413 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (656663719 / 200000000) (1641711123 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (353 / 16000) (1413 / 64000) (1045112985847 / 1000000000000) (1045145646139 / 1000000000000) (656663719 / 200000000) (1641711123 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (353 / 16000) (1413 / 64000) (656663719 / 200000000) (1641711123 / 500000000) (84373 / 1600000000) (26374763 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (656663719 / 200000000) (1641711123 / 500000000) (1850807881 / 1000000000) (462710963 / 250000000) (84373 / 1600000000) (26374763 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0164 :
    ∀ t ∈ Set.Icc ((1413 / 64000) : ℝ) (707 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((522572823069 / 500000000000) : ℝ) ≤ Real.exp (2 * (1413 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1413 / 64000)) (522572823069 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((707 / 32000) : ℝ)) ≤ (20903566149 / 20000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (707 / 32000)) (20903566149 / 20000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((57838859 / 31250000) : ℝ) ≤ Real.exp (3 * (8208553 / 2500000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (8208553 / 2500000) / 16) (57838859 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((656704971 / 200000000) : ℝ) / 16) ≤ (1850879461 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (656704971 / 200000000) / 16) (1850879461 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1413 / 64000) : ℝ) (707 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (8208553 / 2500000) (656704971 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1413 / 64000) (707 / 32000) (522572823069 / 500000000000) (20903566149 / 20000000000) (8208553 / 2500000) (656704971 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1413 / 64000) (707 / 32000) (8208553 / 2500000) (656704971 / 200000000) (26358447 / 500000000000) (52733291 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (8208553 / 2500000) (656704971 / 200000000) (57838859 / 31250000) (1850879461 / 1000000000) (26358447 / 500000000000) (52733291 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0165 :
    ∀ t ∈ Set.Icc ((707 / 32000) : ℝ) (283 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1045178307449 / 1000000000000) : ℝ) ≤ Real.exp (2 * (707 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (707 / 32000)) (1045178307449 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((283 / 12800) : ℝ)) ≤ (1045210969783 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (283 / 12800)) (1045210969783 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1850879097 / 1000000000) : ℝ) ≤ Real.exp (3 * (3283523809 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3283523809 / 1000000000) / 16) (1850879097 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3283627467 / 1000000000) : ℝ) / 16) ≤ (7230137 / 3906250) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3283627467 / 1000000000) / 16) (7230137 / 3906250) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((707 / 32000) : ℝ) (283 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3283523809 / 1000000000) (3283627467 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (707 / 32000) (283 / 12800) (1045178307449 / 1000000000000) (1045210969783 / 1000000000000) (3283523809 / 1000000000) (3283627467 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (707 / 32000) (283 / 12800) (3283523809 / 1000000000) (3283627467 / 1000000000) (52700669 / 1000000000000) (52717061 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3283523809 / 1000000000) (3283627467 / 1000000000) (1850879097 / 1000000000) (7230137 / 3906250) (52700669 / 1000000000000) (52717061 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0166 :
    ∀ t ∈ Set.Icc ((283 / 12800) : ℝ) (177 / 8000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((522605484891 / 500000000000) : ℝ) ≤ Real.exp (2 * (283 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (283 / 12800)) (522605484891 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((177 / 8000) : ℝ)) ≤ (65327727071 / 62500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (177 / 8000)) (65327727071 / 62500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((462728677 / 250000000) : ℝ) ≤ Real.exp (3 * (164181321 / 50000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (164181321 / 50000000) / 16) (462728677 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1641865041 / 500000000) : ℝ) / 16) ≤ (370190137 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1641865041 / 500000000) / 16) (370190137 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((283 / 12800) : ℝ) (177 / 8000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (164181321 / 50000000) (1641865041 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (283 / 12800) (177 / 8000) (522605484891 / 500000000000) (65327727071 / 62500000000) (164181321 / 50000000) (1641865041 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (283 / 12800) (177 / 8000) (164181321 / 50000000) (1641865041 / 500000000) (52684447 / 1000000000000) (10540167 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (164181321 / 50000000) (1641865041 / 500000000) (462728677 / 250000000) (370190137 / 200000000) (52684447 / 1000000000000) (10540167 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0167 :
    ∀ t ∈ Set.Icc ((177 / 8000) : ℝ) (1417 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((209048726627 / 200000000000) : ℝ) ≤ Real.exp (2 * (177 / 8000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (177 / 8000)) (209048726627 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1417 / 64000) : ℝ)) ≤ (104527629751 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1417 / 64000)) (104527629751 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((23136879 / 12500000) : ℝ) ≤ Real.exp (3 * (656745807 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (656745807 / 200000000) / 16) (23136879 / 12500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((32838327 / 10000000) : ℝ) / 16) ≤ (1850986299 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (32838327 / 10000000) / 16) (1850986299 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((177 / 8000) : ℝ) (1417 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (656745807 / 200000000) (32838327 / 10000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (177 / 8000) (1417 / 64000) (209048726627 / 200000000000) (104527629751 / 100000000000) (656745807 / 200000000) (32838327 / 10000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (177 / 8000) (1417 / 64000) (656745807 / 200000000) (32838327 / 10000000) (52668231 / 1000000000000) (10536923 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (656745807 / 200000000) (32838327 / 10000000) (23136879 / 12500000) (1850986299 / 1000000000) (52668231 / 1000000000000) (10536923 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0168 :
    ∀ t ∈ Set.Icc ((1417 / 64000) : ℝ) (709 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1045276297509 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1417 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1417 / 64000)) (1045276297509 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((709 / 32000) : ℝ)) ≤ (209061792581 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (709 / 32000)) (209061792581 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((370197187 / 200000000) : ℝ) ≤ Real.exp (3 * (1641915827 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1641915827 / 500000000) / 16) (370197187 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3283935321 / 1000000000) : ℝ) / 16) ≤ (370204383 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3283935321 / 1000000000) / 16) (370204383 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1417 / 64000) : ℝ) (709 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1641915827 / 500000000) (3283935321 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1417 / 64000) (709 / 32000) (1045276297509 / 1000000000000) (209061792581 / 200000000000) (1641915827 / 500000000) (3283935321 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1417 / 64000) (709 / 32000) (1641915827 / 500000000) (3283935321 / 1000000000) (52652019 / 1000000000000) (26334199 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1641915827 / 500000000) (3283935321 / 1000000000) (370197187 / 200000000) (370204383 / 200000000) (52652019 / 1000000000000) (26334199 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0169 :
    ∀ t ∈ Set.Icc ((709 / 32000) : ℝ) (1419 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((130663620363 / 125000000000) : ℝ) ≤ Real.exp (2 * (709 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (709 / 32000)) (130663620363 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1419 / 64000) : ℝ)) ≤ (26133540733 / 25000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1419 / 64000)) (26133540733 / 25000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1851021551 / 1000000000) : ℝ) ≤ Real.exp (3 * (131357371 / 40000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (131357371 / 40000000) / 16) (1851021551 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1642018973 / 500000000) : ℝ) / 16) ≤ (1851057533 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1642018973 / 500000000) / 16) (1851057533 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((709 / 32000) : ℝ) (1419 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (131357371 / 40000000) (1642018973 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (709 / 32000) (1419 / 64000) (130663620363 / 125000000000) (26133540733 / 25000000000) (131357371 / 40000000) (1642018973 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (709 / 32000) (1419 / 64000) (131357371 / 40000000) (1642018973 / 500000000) (52635811 / 1000000000000) (10530437 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (131357371 / 40000000) (1642018973 / 500000000) (1851021551 / 1000000000) (1851057533 / 1000000000) (52635811 / 1000000000000) (10530437 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0170 :
    ∀ t ∈ Set.Icc ((1419 / 64000) : ℝ) (71 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1045341629319 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1419 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1419 / 64000)) (1045341629319 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((71 / 3200) : ℝ)) ≤ (1045374296757 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (71 / 3200)) (1045374296757 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((115691073 / 62500000) : ℝ) ≤ Real.exp (3 * (3284036899 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3284036899 / 1000000000) / 16) (115691073 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1642070287 / 500000000) : ℝ) / 16) ≤ (1851093153 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1642070287 / 500000000) / 16) (1851093153 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1419 / 64000) : ℝ) (71 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3284036899 / 1000000000) (1642070287 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1419 / 64000) (71 / 3200) (1045341629319 / 1000000000000) (1045374296757 / 1000000000000) (3284036899 / 1000000000) (1642070287 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1419 / 64000) (71 / 3200) (3284036899 / 1000000000) (1642070287 / 500000000) (6577451 / 125000000000) (26317989 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3284036899 / 1000000000) (1642070287 / 500000000) (115691073 / 62500000) (1851093153 / 1000000000) (6577451 / 125000000000) (26317989 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0171 :
    ∀ t ∈ Set.Icc ((71 / 3200) : ℝ) (1421 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((261343574189 / 250000000000) : ℝ) ≤ Real.exp (2 * (71 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (71 / 3200)) (261343574189 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1421 / 64000) : ℝ)) ≤ (522703482607 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1421 / 64000)) (522703482607 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((462773197 / 250000000) : ℝ) ≤ Real.exp (3 * (3284139527 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3284139527 / 1000000000) / 16) (462773197 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((656848641 / 200000000) : ℝ) / 16) ≤ (925564387 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (656848641 / 200000000) / 16) (925564387 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((71 / 3200) : ℝ) (1421 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3284139527 / 1000000000) (656848641 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (71 / 3200) (1421 / 64000) (261343574189 / 250000000000) (522703482607 / 500000000000) (3284139527 / 1000000000) (656848641 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (71 / 3200) (1421 / 64000) (3284139527 / 1000000000) (656848641 / 200000000) (52603409 / 1000000000000) (2104791 / 40000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3284139527 / 1000000000) (656848641 / 200000000) (462773197 / 250000000) (925564387 / 500000000) (52603409 / 1000000000000) (2104791 / 40000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0172 :
    ∀ t ∈ Set.Icc ((1421 / 64000) : ℝ) (711 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1045406965213 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1421 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1421 / 64000)) (1045406965213 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((711 / 32000) : ℝ)) ≤ (261359908673 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (711 / 32000)) (261359908673 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((185112841 / 100000000) : ℝ) ≤ Real.exp (3 * (1642121079 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1642121079 / 500000000) / 16) (185112841 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3284345839 / 1000000000) : ℝ) / 16) ≤ (1851164397 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3284345839 / 1000000000) / 16) (1851164397 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1421 / 64000) : ℝ) (711 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1642121079 / 500000000) (3284345839 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1421 / 64000) (711 / 32000) (1045406965213 / 1000000000000) (261359908673 / 250000000000) (1642121079 / 500000000) (3284345839 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1421 / 64000) (711 / 32000) (1642121079 / 500000000) (3284345839 / 1000000000) (10517443 / 200000000000) (6575447 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1642121079 / 500000000) (3284345839 / 1000000000) (185112841 / 100000000) (1851164397 / 1000000000) (10517443 / 200000000000) (6575447 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0173 :
    ∀ t ∈ Set.Icc ((711 / 32000) : ℝ) (1423 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1045439634691 / 1000000000000) : ℝ) ≤ Real.exp (2 * (711 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (711 / 32000)) (1045439634691 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1423 / 64000) : ℝ)) ≤ (1045472305191 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1423 / 64000)) (1045472305191 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1851164033 / 1000000000) : ℝ) ≤ Real.exp (3 * (410543099 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (410543099 / 125000000) / 16) (1851164033 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((821112119 / 250000000) : ℝ) / 16) ≤ (925600011 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (821112119 / 250000000) / 16) (925600011 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((711 / 32000) : ℝ) (1423 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (410543099 / 125000000) (821112119 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (711 / 32000) (1423 / 64000) (1045439634691 / 1000000000000) (1045472305191 / 1000000000000) (410543099 / 125000000) (821112119 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (711 / 32000) (1423 / 64000) (410543099 / 125000000) (821112119 / 250000000) (2102841 / 40000000000) (52587381 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (410543099 / 125000000) (821112119 / 250000000) (1851164033 / 1000000000) (925600011 / 500000000) (2102841 / 40000000000) (52587381 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0174 :
    ∀ t ∈ Set.Icc ((1423 / 64000) : ℝ) (89 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((104547230519 / 100000000000) : ℝ) ≤ Real.exp (2 * (1423 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1423 / 64000)) (104547230519 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((89 / 4000) : ℝ)) ≤ (1045504976711 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (89 / 4000)) (1045504976711 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((925599829 / 500000000) : ℝ) ≤ Real.exp (3 * (328444743 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (328444743 / 100000000) / 16) (925599829 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3284551117 / 1000000000) : ℝ) / 16) ≤ (1851235649 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3284551117 / 1000000000) / 16) (1851235649 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1423 / 64000) : ℝ) (89 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (328444743 / 100000000) (3284551117 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1423 / 64000) (89 / 4000) (104547230519 / 100000000000) (1045504976711 / 1000000000000) (328444743 / 100000000) (3284551117 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1423 / 64000) (89 / 4000) (328444743 / 100000000) (3284551117 / 1000000000) (1313871 / 25000000000) (6571399 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (328444743 / 100000000) (3284551117 / 1000000000) (925599829 / 500000000) (1851235649 / 1000000000) (1313871 / 25000000000) (6571399 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0175 :
    ∀ t ∈ Set.Icc ((89 / 4000) : ℝ) (57 / 2560), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((104550497671 / 100000000000) : ℝ) ≤ Real.exp (2 * (89 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (89 / 4000)) (104550497671 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((57 / 2560) : ℝ)) ≤ (261384412313 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (57 / 2560)) (261384412313 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((370247057 / 200000000) : ℝ) ≤ Real.exp (3 * (328455007 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (328455007 / 100000000) / 16) (370247057 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3284653761 / 1000000000) : ℝ) / 16) ≤ (925635639 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3284653761 / 1000000000) / 16) (925635639 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((89 / 4000) : ℝ) (57 / 2560),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (328455007 / 100000000) (3284653761 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (89 / 4000) (57 / 2560) (104550497671 / 100000000000) (261384412313 / 250000000000) (328455007 / 100000000) (3284653761 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (89 / 4000) (57 / 2560) (328455007 / 100000000) (3284653761 / 1000000000) (52538659 / 1000000000000) (26277503 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (328455007 / 100000000) (3284653761 / 1000000000) (370247057 / 200000000) (925635639 / 500000000) (52538659 / 1000000000000) (26277503 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0176 :
    ∀ t ∈ Set.Icc ((57 / 2560) : ℝ) (713 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1045537649251 / 1000000000000) : ℝ) ≤ Real.exp (2 * (57 / 2560)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (57 / 2560)) (1045537649251 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((713 / 32000) : ℝ)) ≤ (522785161407 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (713 / 32000)) (522785161407 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((925635457 / 500000000) : ℝ) ≤ Real.exp (3 * (1642326357 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1642326357 / 500000000) / 16) (925635457 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((410594551 / 125000000) : ℝ) / 16) ≤ (1851306909 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (410594551 / 125000000) / 16) (1851306909 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((57 / 2560) : ℝ) (713 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1642326357 / 500000000) (410594551 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (57 / 2560) (713 / 32000) (1045537649251 / 1000000000000) (522785161407 / 500000000000) (1642326357 / 500000000) (410594551 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (57 / 2560) (713 / 32000) (1642326357 / 500000000) (410594551 / 125000000) (52522483 / 1000000000000) (2101553 / 40000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1642326357 / 500000000) (410594551 / 125000000) (925635457 / 500000000) (1851306909 / 1000000000) (52522483 / 1000000000000) (2101553 / 40000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0177 :
    ∀ t ∈ Set.Icc ((713 / 32000) : ℝ) (1427 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1045570322813 / 1000000000000) : ℝ) ≤ Real.exp (2 * (713 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (713 / 32000)) (1045570322813 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1427 / 64000) : ℝ)) ≤ (1045602997397 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1427 / 64000)) (1045602997397 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((115706659 / 62500000) : ℝ) ≤ Real.exp (3 * (3284755361 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3284755361 / 1000000000) / 16) (115706659 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1642429529 / 500000000) : ℝ) / 16) ≤ (1851342541 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1642429529 / 500000000) / 16) (1851342541 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((713 / 32000) : ℝ) (1427 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3284755361 / 1000000000) (1642429529 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (713 / 32000) (1427 / 64000) (1045570322813 / 1000000000000) (1045602997397 / 1000000000000) (3284755361 / 1000000000) (1642429529 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (713 / 32000) (1427 / 64000) (3284755361 / 1000000000) (1642429529 / 500000000) (52506311 / 1000000000000) (52522649 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3284755361 / 1000000000) (1642429529 / 500000000) (115706659 / 62500000) (1851342541 / 1000000000) (52506311 / 1000000000000) (52522649 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0178 :
    ∀ t ∈ Set.Icc ((1427 / 64000) : ℝ) (357 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((261400749349 / 250000000000) : ℝ) ≤ Real.exp (2 * (1427 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1427 / 64000)) (261400749349 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((357 / 16000) : ℝ)) ≤ (1045635673001 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (357 / 16000)) (1045635673001 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((57854443 / 31250000) : ℝ) ≤ Real.exp (3 * (3284858011 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3284858011 / 1000000000) / 16) (57854443 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3284961711 / 1000000000) : ℝ) / 16) ≤ (74055127 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3284961711 / 1000000000) / 16) (74055127 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1427 / 64000) : ℝ) (357 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3284858011 / 1000000000) (3284961711 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1427 / 64000) (357 / 16000) (261400749349 / 250000000000) (1045635673001 / 1000000000000) (3284858011 / 1000000000) (3284961711 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1427 / 64000) (357 / 16000) (3284858011 / 1000000000) (3284961711 / 1000000000) (1640317 / 31250000000) (52506477 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3284858011 / 1000000000) (3284961711 / 1000000000) (57854443 / 31250000) (74055127 / 40000000) (1640317 / 31250000000) (52506477 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0179 :
    ∀ t ∈ Set.Icc ((357 / 16000) : ℝ) (1429 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1045635673 / 1000000000) : ℝ) ≤ Real.exp (2 * (357 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (357 / 16000)) (1045635673 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1429 / 64000) : ℝ)) ≤ (1045668349627 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1429 / 64000)) (1045668349627 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1851377811 / 1000000000) : ℝ) ≤ Real.exp (3 * (656992133 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (656992133 / 200000000) / 16) (1851377811 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((205316523 / 62500000) : ℝ) / 16) ≤ (1851413811 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (205316523 / 62500000) / 16) (1851413811 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((357 / 16000) : ℝ) (1429 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (656992133 / 200000000) (205316523 / 62500000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (357 / 16000) (1429 / 64000) (1045635673 / 1000000000) (1045668349627 / 1000000000000) (656992133 / 200000000) (205316523 / 62500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (357 / 16000) (1429 / 64000) (656992133 / 200000000) (205316523 / 62500000) (52473981 / 1000000000000) (5249031 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (656992133 / 200000000) (205316523 / 62500000) (1851377811 / 1000000000) (1851413811 / 1000000000) (52473981 / 1000000000000) (5249031 / 100000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch008 :
    ∀ t ∈ Set.Icc ((1409 / 64000) : ℝ) (1429 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0160
      hpThetaDensityTwoTermCompact_cell0161)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0162
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0163
      hpThetaDensityTwoTermCompact_cell0164)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0165
      hpThetaDensityTwoTermCompact_cell0166)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0167
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0168
      hpThetaDensityTwoTermCompact_cell0169))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0170
      hpThetaDensityTwoTermCompact_cell0171)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0172
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0173
      hpThetaDensityTwoTermCompact_cell0174)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0175
      hpThetaDensityTwoTermCompact_cell0176)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0177
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0178
      hpThetaDensityTwoTermCompact_cell0179)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch008
end HodgeProofHP
