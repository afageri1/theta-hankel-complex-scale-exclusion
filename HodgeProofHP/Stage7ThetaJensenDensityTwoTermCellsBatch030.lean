/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0600 :
    ∀ t ∈ Set.Icc ((409 / 12800) : ℝ) (2047 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1065992457283 / 1000000000000) : ℝ) ≤ Real.exp (2 * (409 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (409 / 12800)) (1065992457283 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2047 / 64000) : ℝ)) ≤ (213211816779 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2047 / 64000)) (213211816779 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((468427891 / 250000000) : ℝ) ≤ Real.exp (3 * (26791307 / 8000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (26791307 / 8000000) / 16) (468427891 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((837280939 / 250000000) : ℝ) / 16) ≤ (936892739 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (837280939 / 250000000) / 16) (936892739 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((409 / 12800) : ℝ) (2047 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (26791307 / 8000000) (837280939 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (409 / 12800) (2047 / 64000) (1065992457283 / 1000000000000) (213211816779 / 200000000000) (26791307 / 8000000) (837280939 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (409 / 12800) (2047 / 64000) (26791307 / 8000000) (837280939 / 250000000) (21649711 / 500000000000) (1083169 / 25000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (26791307 / 8000000) (837280939 / 250000000) (468427891 / 250000000) (936892739 / 500000000) (21649711 / 500000000000) (1083169 / 25000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0601 :
    ∀ t ∈ Set.Icc ((2047 / 64000) : ℝ) (2049 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((533029541947 / 500000000000) : ℝ) ≤ Real.exp (2 * (2047 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2047 / 64000)) (533029541947 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2049 / 64000) : ℝ)) ≤ (106612571467 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2049 / 64000)) (106612571467 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((936892551 / 500000000) : ℝ) ≤ Real.exp (3 * (3349122689 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3349122689 / 1000000000) / 16) (936892551 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3349333083 / 1000000000) : ℝ) / 16) ≤ (1873859023 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3349333083 / 1000000000) / 16) (1873859023 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2047 / 64000) : ℝ) (2049 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3349122689 / 1000000000) (3349333083 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2047 / 64000) (2049 / 64000) (533029541947 / 500000000000) (106612571467 / 100000000000) (3349122689 / 1000000000) (3349333083 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2047 / 64000) (2049 / 64000) (3349122689 / 1000000000) (3349333083 / 1000000000) (43272239 / 1000000000000) (21649781 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3349122689 / 1000000000) (3349333083 / 1000000000) (936892551 / 500000000) (1873859023 / 1000000000) (43272239 / 1000000000000) (21649781 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0602 :
    ∀ t ∈ Set.Icc ((2049 / 64000) : ℝ) (2051 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1066125714669 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2049 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2049 / 64000)) (1066125714669 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2051 / 64000) : ℝ)) ≤ (106619234961 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2051 / 64000)) (106619234961 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1873858647 / 1000000000) : ℝ) ≤ Real.exp (3 * (209333251 / 62500000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (209333251 / 62500000) / 16) (1873858647 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3349542423 / 1000000000) : ℝ) / 16) ≤ (58560393 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3349542423 / 1000000000) / 16) (58560393 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2049 / 64000) : ℝ) (2051 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (209333251 / 62500000) (3349542423 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2049 / 64000) (2051 / 64000) (1066125714669 / 1000000000000) (106619234961 / 100000000000) (209333251 / 62500000) (3349542423 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2049 / 64000) (2051 / 64000) (209333251 / 62500000) (3349542423 / 1000000000) (2702817 / 62500000000) (43272379 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (209333251 / 62500000) (3349542423 / 1000000000) (1873858647 / 1000000000) (58560393 / 31250000) (2702817 / 62500000000) (43272379 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0603 :
    ∀ t ∈ Set.Icc ((2051 / 64000) : ℝ) (2053 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1066192349609 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2051 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2051 / 64000)) (1066192349609 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2053 / 64000) : ℝ)) ≤ (533129494357 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2053 / 64000)) (533129494357 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((9369661 / 5000000) : ℝ) ≤ Real.exp (3 * (669908271 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (669908271 / 200000000) / 16) (9369661 / 5000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((104679743 / 31250000) : ℝ) / 16) ≤ (234250767 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (104679743 / 31250000) / 16) (234250767 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2051 / 64000) : ℝ) (2053 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (669908271 / 200000000) (104679743 / 31250000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2051 / 64000) (2053 / 64000) (1066192349609 / 1000000000000) (533129494357 / 500000000000) (669908271 / 200000000) (104679743 / 31250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2051 / 64000) (2053 / 64000) (669908271 / 200000000) (104679743 / 31250000) (8441 / 195312500) (43245211 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (669908271 / 200000000) (104679743 / 31250000) (9369661 / 5000000) (234250767 / 125000000) (8441 / 195312500) (43245211 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0604 :
    ∀ t ∈ Set.Icc ((2053 / 64000) : ℝ) (411 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1066258988713 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2053 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2053 / 64000)) (1066258988713 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((411 / 12800) : ℝ)) ≤ (1066325631983 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (411 / 12800)) (1066325631983 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1464067 / 781250) : ℝ) ≤ Real.exp (3 * (837437677 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (837437677 / 250000000) / 16) (1464067 / 781250) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1674980571 / 500000000) : ℝ) / 16) ≤ (234259963 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1674980571 / 500000000) / 16) (234259963 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2053 / 64000) : ℝ) (411 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (837437677 / 250000000) (1674980571 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2053 / 64000) (411 / 12800) (1066258988713 / 1000000000000) (1066325631983 / 1000000000000) (837437677 / 250000000) (1674980571 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2053 / 64000) (411 / 12800) (837437677 / 250000000) (1674980571 / 500000000) (43190783 / 1000000000000) (43218059 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (837437677 / 250000000) (1674980571 / 500000000) (1464067 / 781250) (234259963 / 125000000) (43190783 / 1000000000000) (43218059 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0605 :
    ∀ t ∈ Set.Icc ((411 / 12800) : ℝ) (2057 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((533162815991 / 500000000000) : ℝ) ≤ Real.exp (2 * (411 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (411 / 12800)) (533162815991 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2057 / 64000) : ℝ)) ≤ (533196139709 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2057 / 64000)) (533196139709 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((58564979 / 31250000) : ℝ) ≤ Real.exp (3 * (1674980037 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1674980037 / 500000000) / 16) (58564979 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3350170521 / 1000000000) : ℝ) / 16) ≤ (1874153279 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3350170521 / 1000000000) / 16) (1874153279 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((411 / 12800) : ℝ) (2057 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1674980037 / 500000000) (3350170521 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (411 / 12800) (2057 / 64000) (533162815991 / 500000000000) (533196139709 / 500000000000) (1674980037 / 500000000) (3350170521 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (411 / 12800) (2057 / 64000) (1674980037 / 500000000) (3350170521 / 1000000000) (21581831 / 500000000000) (43190923 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1674980037 / 500000000) (3350170521 / 1000000000) (58564979 / 31250000) (1874153279 / 1000000000) (21581831 / 500000000000) (43190923 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0606 :
    ∀ t ∈ Set.Icc ((2057 / 64000) : ℝ) (2059 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1066392279417 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2057 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2057 / 64000)) (1066392279417 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2059 / 64000) : ℝ)) ≤ (533229465509 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2059 / 64000)) (533229465509 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1874152903 / 1000000000) : ℝ) ≤ Real.exp (3 * (3350169453 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3350169453 / 1000000000) / 16) (1874152903 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3350379913 / 1000000000) : ℝ) / 16) ≤ (937113431 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3350379913 / 1000000000) / 16) (937113431 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2057 / 64000) : ℝ) (2059 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3350169453 / 1000000000) (3350379913 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2057 / 64000) (2059 / 64000) (1066392279417 / 1000000000000) (533229465509 / 500000000000) (3350169453 / 1000000000) (3350379913 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2057 / 64000) (2059 / 64000) (3350169453 / 1000000000) (3350379913 / 1000000000) (10784139 / 250000000000) (43163801 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3350169453 / 1000000000) (3350379913 / 1000000000) (1874152903 / 1000000000) (937113431 / 500000000) (10784139 / 250000000000) (43163801 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0607 :
    ∀ t ∈ Set.Icc ((2059 / 64000) : ℝ) (2061 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1066458931017 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2059 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2059 / 64000)) (1066458931017 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2061 / 64000) : ℝ)) ≤ (33328924587 / 31250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2061 / 64000)) (33328924587 / 31250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((937113243 / 500000000) : ℝ) ≤ Real.exp (3 * (1675189423 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1675189423 / 500000000) / 16) (937113243 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1675294659 / 500000000) : ℝ) / 16) ≤ (468575113 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1675294659 / 500000000) / 16) (468575113 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2059 / 64000) : ℝ) (2061 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1675189423 / 500000000) (1675294659 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2059 / 64000) (2061 / 64000) (1066458931017 / 1000000000000) (33328924587 / 31250000000) (1675189423 / 500000000) (1675294659 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2059 / 64000) (2061 / 64000) (1675189423 / 500000000) (1675294659 / 500000000) (8621893 / 200000000000) (8627339 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1675189423 / 500000000) (1675294659 / 500000000) (937113243 / 500000000) (468575113 / 250000000) (8621893 / 200000000000) (8627339 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0608 :
    ∀ t ∈ Set.Icc ((2061 / 64000) : ℝ) (2063 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1066525586783 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2061 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2061 / 64000)) (1066525586783 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2063 / 64000) : ℝ)) ≤ (1066592246717 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2063 / 64000)) (1066592246717 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((468575019 / 250000000) : ℝ) ≤ Real.exp (3 * (3350588251 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3350588251 / 1000000000) / 16) (468575019 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3350798737 / 1000000000) : ℝ) / 16) ≤ (37487481 / 20000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3350798737 / 1000000000) / 16) (37487481 / 20000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2061 / 64000) : ℝ) (2063 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3350588251 / 1000000000) (3350798737 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2061 / 64000) (2063 / 64000) (1066525586783 / 1000000000000) (1066592246717 / 1000000000000) (3350588251 / 1000000000) (3350798737 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2061 / 64000) (2063 / 64000) (3350588251 / 1000000000) (3350798737 / 1000000000) (4308239 / 100000000000) (8621921 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3350588251 / 1000000000) (3350798737 / 1000000000) (468575019 / 250000000) (37487481 / 20000000) (4308239 / 100000000000) (8621921 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0609 :
    ∀ t ∈ Set.Icc ((2063 / 64000) : ℝ) (413 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((266648061679 / 250000000000) : ℝ) ≤ Real.exp (2 * (2063 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2063 / 64000)) (266648061679 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((413 / 12800) : ℝ)) ≤ (213331782163 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (413 / 12800)) (213331782163 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1874373673 / 1000000000) : ℝ) ≤ Real.exp (3 * (3350797669 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3350797669 / 1000000000) / 16) (1874373673 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((418876021 / 125000000) : ℝ) / 16) ≤ (374889531 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (418876021 / 125000000) / 16) (374889531 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2063 / 64000) : ℝ) (413 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3350797669 / 1000000000) (418876021 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2063 / 64000) (413 / 12800) (266648061679 / 250000000000) (213331782163 / 200000000000) (3350797669 / 1000000000) (418876021 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2063 / 64000) (413 / 12800) (3350797669 / 1000000000) (418876021 / 125000000) (4305533 / 100000000000) (4308253 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3350797669 / 1000000000) (418876021 / 125000000) (1874373673 / 1000000000) (374889531 / 200000000) (4305533 / 100000000000) (4308253 / 100000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0610 :
    ∀ t ∈ Set.Icc ((413 / 12800) : ℝ) (2067 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((533329455407 / 500000000000) : ℝ) ≤ Real.exp (2 * (413 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (413 / 12800)) (533329455407 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2067 / 64000) : ℝ)) ≤ (1066725579081 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2067 / 64000)) (1066725579081 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((937223639 / 500000000) : ℝ) ≤ Real.exp (3 * (33510071 / 10000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (33510071 / 10000000) / 16) (937223639 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3351217613 / 1000000000) : ℝ) / 16) ≤ (1874521267 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3351217613 / 1000000000) / 16) (1874521267 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((413 / 12800) : ℝ) (2067 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (33510071 / 10000000) (3351217613 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (413 / 12800) (2067 / 64000) (533329455407 / 500000000000) (1066725579081 / 1000000000000) (33510071 / 10000000) (3351217613 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (413 / 12800) (2067 / 64000) (33510071 / 10000000) (3351217613 / 1000000000) (21514143 / 500000000000) (4305547 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (33510071 / 10000000) (3351217613 / 1000000000) (937223639 / 500000000) (1874521267 / 1000000000) (21514143 / 500000000000) (4305547 / 100000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0611 :
    ∀ t ∈ Set.Icc ((2067 / 64000) : ℝ) (2069 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((26668139477 / 25000000000) : ℝ) ≤ Real.exp (2 * (2067 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2067 / 64000)) (26668139477 / 25000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2069 / 64000) : ℝ)) ≤ (1066792251513 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2069 / 64000)) (1066792251513 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1874520891 / 1000000000) : ℝ) ≤ Real.exp (3 * (670243309 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (670243309 / 200000000) / 16) (1874520891 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((335142707 / 100000000) : ℝ) / 16) ≤ (1874594887 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (335142707 / 100000000) / 16) (1874594887 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2067 / 64000) : ℝ) (2069 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (670243309 / 200000000) (335142707 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2067 / 64000) (2069 / 64000) (26668139477 / 25000000000) (1066792251513 / 1000000000000) (670243309 / 200000000) (335142707 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2067 / 64000) (2069 / 64000) (670243309 / 200000000) (335142707 / 100000000) (5375157 / 125000000000) (1721137 / 40000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (670243309 / 200000000) (335142707 / 100000000) (1874520891 / 1000000000) (1874594887 / 1000000000) (5375157 / 125000000000) (1721137 / 40000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0612 :
    ∀ t ∈ Set.Icc ((2069 / 64000) : ℝ) (2071 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((133349031439 / 125000000000) : ℝ) ≤ Real.exp (2 * (2069 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2069 / 64000)) (133349031439 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2071 / 64000) : ℝ)) ≤ (66678683007 / 62500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2071 / 64000)) (66678683007 / 62500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1874594511 / 1000000000) : ℝ) ≤ Real.exp (3 * (3351426003 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3351426003 / 1000000000) / 16) (1874594511 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3351636541 / 1000000000) : ℝ) / 16) ≤ (374933703 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3351636541 / 1000000000) / 16) (374933703 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2069 / 64000) : ℝ) (2071 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3351426003 / 1000000000) (3351636541 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2069 / 64000) (2071 / 64000) (133349031439 / 125000000000) (66678683007 / 62500000000) (3351426003 / 1000000000) (3351636541 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2069 / 64000) (2071 / 64000) (3351426003 / 1000000000) (3351636541 / 1000000000) (21487121 / 500000000000) (8600279 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3351426003 / 1000000000) (3351636541 / 1000000000) (1874594511 / 1000000000) (374933703 / 200000000) (21487121 / 500000000000) (8600279 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0613 :
    ∀ t ∈ Set.Icc ((2071 / 64000) : ℝ) (2073 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1066858928111 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2071 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2071 / 64000)) (1066858928111 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2073 / 64000) : ℝ)) ≤ (1066925608879 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2073 / 64000)) (1066925608879 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((937334069 / 500000000) : ℝ) ≤ Real.exp (3 * (3351635473 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3351635473 / 1000000000) / 16) (937334069 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((134073841 / 40000000) : ℝ) / 16) ≤ (37494843 / 20000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (134073841 / 40000000) / 16) (37494843 / 20000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2071 / 64000) : ℝ) (2073 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3351635473 / 1000000000) (134073841 / 40000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2071 / 64000) (2073 / 64000) (1066858928111 / 1000000000000) (1066925608879 / 1000000000000) (3351635473 / 1000000000) (134073841 / 40000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2071 / 64000) (2073 / 64000) (3351635473 / 1000000000) (134073841 / 40000000) (42947243 / 1000000000000) (42974381 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3351635473 / 1000000000) (134073841 / 40000000) (937334069 / 500000000) (37494843 / 20000000) (42947243 / 1000000000000) (42974381 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0614 :
    ∀ t ∈ Set.Icc ((2073 / 64000) : ℝ) (83 / 2560), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((533462804439 / 500000000000) : ℝ) ≤ Real.exp (2 * (2073 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2073 / 64000)) (533462804439 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((83 / 2560) : ℝ)) ≤ (1066992293813 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (83 / 2560)) (1066992293813 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((937370887 / 500000000) : ℝ) ≤ Real.exp (3 * (3351844957 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3351844957 / 1000000000) / 16) (937370887 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1676027761 / 500000000) : ℝ) / 16) ≤ (1874815793 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1676027761 / 500000000) / 16) (1874815793 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2073 / 64000) : ℝ) (83 / 2560),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3351844957 / 1000000000) (1676027761 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2073 / 64000) (83 / 2560) (533462804439 / 500000000000) (1066992293813 / 1000000000000) (3351844957 / 1000000000) (1676027761 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2073 / 64000) (83 / 2560) (3351844957 / 1000000000) (1676027761 / 500000000) (2146013 / 50000000000) (21473691 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3351844957 / 1000000000) (1676027761 / 500000000) (937370887 / 500000000) (1874815793 / 1000000000) (2146013 / 50000000000) (21473691 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0615 :
    ∀ t ∈ Set.Icc ((83 / 2560) : ℝ) (2077 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((266748073453 / 250000000000) : ℝ) ≤ Real.exp (2 * (83 / 2560)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (83 / 2560)) (266748073453 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2077 / 64000) : ℝ)) ≤ (266764745729 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2077 / 64000)) (266764745729 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((234351927 / 125000000) : ℝ) ≤ Real.exp (3 * (1676027227 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1676027227 / 500000000) / 16) (234351927 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((419033129 / 125000000) : ℝ) / 16) ≤ (1874889443 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (419033129 / 125000000) / 16) (1874889443 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((83 / 2560) : ℝ) (2077 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1676027227 / 500000000) (419033129 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (83 / 2560) (2077 / 64000) (266748073453 / 250000000000) (266764745729 / 250000000000) (1676027227 / 500000000) (419033129 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (83 / 2560) (2077 / 64000) (1676027227 / 500000000) (419033129 / 125000000) (10723323 / 250000000000) (42920399 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1676027227 / 500000000) (419033129 / 125000000) (234351927 / 125000000) (1874889443 / 1000000000) (10723323 / 250000000000) (42920399 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0616 :
    ∀ t ∈ Set.Icc ((2077 / 64000) : ℝ) (2079 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((213411796583 / 200000000000) : ℝ) ≤ Real.exp (2 * (2077 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2077 / 64000)) (213411796583 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2079 / 64000) : ℝ)) ≤ (533562838093 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2079 / 64000)) (533562838093 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((937444533 / 500000000) : ℝ) ≤ Real.exp (3 * (838065991 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (838065991 / 250000000) / 16) (937444533 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((670494911 / 200000000) : ℝ) / 16) ≤ (18749631 / 10000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (670494911 / 200000000) / 16) (18749631 / 10000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2077 / 64000) : ℝ) (2079 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (838065991 / 250000000) (670494911 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2077 / 64000) (2079 / 64000) (213411796583 / 200000000000) (533562838093 / 500000000000) (838065991 / 250000000) (670494911 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2077 / 64000) (2079 / 64000) (838065991 / 250000000) (670494911 / 200000000) (42866339 / 1000000000000) (42893431 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (838065991 / 250000000) (670494911 / 200000000) (937444533 / 500000000) (18749631 / 10000000) (42866339 / 1000000000000) (42893431 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0617 :
    ∀ t ∈ Set.Icc ((2079 / 64000) : ℝ) (2081 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((213425135237 / 200000000000) : ℝ) ≤ Real.exp (2 * (2079 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2079 / 64000)) (213425135237 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2081 / 64000) : ℝ)) ≤ (8537538989 / 8000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2081 / 64000)) (8537538989 / 8000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((468740681 / 250000000) : ℝ) ≤ Real.exp (3 * (3352473487 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3352473487 / 1000000000) / 16) (468740681 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3352684091 / 1000000000) : ℝ) / 16) ≤ (375007353 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3352684091 / 1000000000) / 16) (375007353 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2079 / 64000) : ℝ) (2081 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3352473487 / 1000000000) (3352684091 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2079 / 64000) (2081 / 64000) (213425135237 / 200000000000) (8537538989 / 8000000000) (3352473487 / 1000000000) (3352684091 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2079 / 64000) (2081 / 64000) (3352473487 / 1000000000) (3352684091 / 1000000000) (42839401 / 1000000000000) (21433239 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3352473487 / 1000000000) (3352684091 / 1000000000) (468740681 / 250000000) (375007353 / 200000000) (42839401 / 1000000000000) (21433239 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0618 :
    ∀ t ∈ Set.Icc ((2081 / 64000) : ℝ) (2083 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((133399046703 / 125000000000) : ℝ) ≤ Real.exp (2 * (2081 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2081 / 64000)) (133399046703 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2083 / 64000) : ℝ)) ≤ (1067259075233 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2083 / 64000)) (1067259075233 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1875036389 / 1000000000) : ℝ) ≤ Real.exp (3 * (3352683023 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3352683023 / 1000000000) / 16) (1875036389 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((83822341 / 25000000) : ℝ) / 16) ≤ (937555219 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (83822341 / 25000000) / 16) (937555219 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2081 / 64000) : ℝ) (2083 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3352683023 / 1000000000) (83822341 / 25000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2081 / 64000) (2083 / 64000) (133399046703 / 125000000000) (1067259075233 / 1000000000000) (3352683023 / 1000000000) (83822341 / 25000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2081 / 64000) (2083 / 64000) (3352683023 / 1000000000) (83822341 / 25000000) (42812479 / 1000000000000) (2141977 / 50000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3352683023 / 1000000000) (83822341 / 25000000) (1875036389 / 1000000000) (937555219 / 500000000) (42812479 / 1000000000000) (2141977 / 50000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0619 :
    ∀ t ∈ Set.Icc ((2083 / 64000) : ℝ) (417 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((33351846101 / 31250000000) : ℝ) ≤ Real.exp (2 * (2083 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2083 / 64000)) (33351846101 / 31250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((417 / 12800) : ℝ)) ≤ (106732578101 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (417 / 12800)) (106732578101 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1875110061 / 1000000000) : ℝ) ≤ Real.exp (3 * (838223143 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (838223143 / 250000000) / 16) (1875110061 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3353103203 / 1000000000) : ℝ) / 16) ≤ (937592059 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3353103203 / 1000000000) / 16) (937592059 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2083 / 64000) : ℝ) (417 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (838223143 / 250000000) (3353103203 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2083 / 64000) (417 / 12800) (33351846101 / 31250000000) (106732578101 / 100000000000) (838223143 / 250000000) (3353103203 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2083 / 64000) (417 / 12800) (838223143 / 250000000) (3353103203 / 1000000000) (10696393 / 250000000000) (42812617 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (838223143 / 250000000) (3353103203 / 1000000000) (1875110061 / 1000000000) (937592059 / 500000000) (10696393 / 250000000000) (42812617 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch030 :
    ∀ t ∈ Set.Icc ((409 / 12800) : ℝ) (417 / 12800),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0600
      hpThetaDensityTwoTermCompact_cell0601)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0602
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0603
      hpThetaDensityTwoTermCompact_cell0604)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0605
      hpThetaDensityTwoTermCompact_cell0606)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0607
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0608
      hpThetaDensityTwoTermCompact_cell0609))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0610
      hpThetaDensityTwoTermCompact_cell0611)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0612
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0613
      hpThetaDensityTwoTermCompact_cell0614)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0615
      hpThetaDensityTwoTermCompact_cell0616)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0617
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0618
      hpThetaDensityTwoTermCompact_cell0619)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch030
end HodgeProofHP
