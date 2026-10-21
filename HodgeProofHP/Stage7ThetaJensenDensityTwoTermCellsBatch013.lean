/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0260 :
    ∀ t ∈ Set.Icc ((1509 / 64000) : ℝ) (151 / 6400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((524142895469 / 500000000000) : ℝ) ≤ Real.exp (2 * (1509 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1509 / 64000)) (524142895469 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((151 / 6400) : ℝ)) ≤ (524159275191 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (151 / 6400)) (524159275191 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1854270157 / 1000000000) : ℝ) ≤ Real.exp (3 * (1646643127 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1646643127 / 500000000) / 16) (1854270157 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((164669511 / 50000000) : ℝ) / 16) ≤ (370861261 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (164669511 / 50000000) / 16) (370861261 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1509 / 64000) : ℝ) (151 / 6400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1646643127 / 500000000) (164669511 / 50000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1509 / 64000) (151 / 6400) (524142895469 / 500000000000) (524159275191 / 500000000000) (1646643127 / 500000000) (164669511 / 50000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1509 / 64000) (151 / 6400) (1646643127 / 500000000) (164669511 / 50000000) (25589771 / 500000000000) (51195509 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1646643127 / 500000000) (164669511 / 50000000) (1854270157 / 1000000000) (370861261 / 200000000) (25589771 / 500000000000) (51195509 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0261 :
    ∀ t ∈ Set.Icc ((151 / 6400) : ℝ) (1511 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1048318550381 / 1000000000000) : ℝ) ≤ Real.exp (2 * (151 / 6400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (151 / 6400)) (1048318550381 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1511 / 64000) : ℝ)) ≤ (1048351310849 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1511 / 64000)) (1048351310849 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1854305939 / 1000000000) : ℝ) ≤ Real.exp (3 * (3293389171 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3293389171 / 1000000000) / 16) (1854305939 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((164674657 / 50000000) : ℝ) / 16) ≤ (1854342089 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (164674657 / 50000000) / 16) (1854342089 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((151 / 6400) : ℝ) (1511 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3293389171 / 1000000000) (164674657 / 50000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (151 / 6400) (1511 / 64000) (1048318550381 / 1000000000000) (1048351310849 / 1000000000000) (3293389171 / 1000000000) (164674657 / 50000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (151 / 6400) (1511 / 64000) (3293389171 / 1000000000) (164674657 / 50000000) (25581871 / 500000000000) (10235941 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3293389171 / 1000000000) (164674657 / 50000000) (1854305939 / 1000000000) (1854342089 / 1000000000) (25581871 / 500000000000) (10235941 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0262 :
    ∀ t ∈ Set.Icc ((1511 / 64000) : ℝ) (189 / 8000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1023780577 / 976562500) : ℝ) ≤ Real.exp (2 * (1511 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1511 / 64000)) (1023780577 / 976562500) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((189 / 8000) : ℝ)) ≤ (1048384072339 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (189 / 8000)) (1048384072339 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1854341723 / 1000000000) : ℝ) ≤ Real.exp (3 * (3293492091 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3293492091 / 1000000000) / 16) (1854341723 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3293596063 / 1000000000) : ℝ) / 16) ≤ (927188937 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3293596063 / 1000000000) / 16) (927188937 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1511 / 64000) : ℝ) (189 / 8000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3293492091 / 1000000000) (3293596063 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1511 / 64000) (189 / 8000) (1023780577 / 976562500) (1048384072339 / 1000000000000) (3293492091 / 1000000000) (3293596063 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1511 / 64000) (189 / 8000) (3293492091 / 1000000000) (3293596063 / 1000000000) (51147947 / 1000000000000) (10232781 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3293492091 / 1000000000) (3293596063 / 1000000000) (1854341723 / 1000000000) (927188937 / 500000000) (51147947 / 1000000000000) (10232781 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0263 :
    ∀ t ∈ Set.Icc ((189 / 8000) : ℝ) (1513 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((524192036169 / 500000000000) : ℝ) ≤ Real.exp (2 * (189 / 8000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (189 / 8000)) (524192036169 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1513 / 64000) : ℝ)) ≤ (1048416834853 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1513 / 64000)) (1048416834853 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1854377509 / 1000000000) : ℝ) ≤ Real.exp (3 * (1646797507 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1646797507 / 500000000) / 16) (1854377509 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((329369899 / 100000000) : ℝ) / 16) ≤ (927206831 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (329369899 / 100000000) / 16) (927206831 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((189 / 8000) : ℝ) (1513 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1646797507 / 500000000) (329369899 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (189 / 8000) (1513 / 64000) (524192036169 / 500000000000) (1048416834853 / 1000000000000) (1646797507 / 500000000) (329369899 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (189 / 8000) (1513 / 64000) (1646797507 / 500000000) (329369899 / 100000000) (12783039 / 250000000000) (51148109 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1646797507 / 500000000) (329369899 / 100000000) (1854377509 / 1000000000) (927206831 / 500000000) (12783039 / 250000000000) (51148109 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0264 :
    ∀ t ∈ Set.Icc ((1513 / 64000) : ℝ) (757 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((262104208713 / 250000000000) : ℝ) ≤ Real.exp (2 * (1513 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1513 / 64000)) (262104208713 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((757 / 32000) : ℝ)) ≤ (1048449598391 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (757 / 32000)) (1048449598391 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((115900831 / 62500000) : ℝ) ≤ Real.exp (3 * (3293697941 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3293697941 / 1000000000) / 16) (115900831 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((10293131 / 3125000) : ℝ) / 16) ≤ (1854449451 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (10293131 / 3125000) / 16) (1854449451 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1513 / 64000) : ℝ) (757 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3293697941 / 1000000000) (10293131 / 3125000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1513 / 64000) (757 / 32000) (262104208713 / 250000000000) (1048449598391 / 1000000000000) (3293697941 / 1000000000) (10293131 / 3125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1513 / 64000) (757 / 32000) (3293697941 / 1000000000) (10293131 / 3125000) (51116369 / 1000000000000) (25566159 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3293697941 / 1000000000) (10293131 / 3125000) (115900831 / 62500000) (1854449451 / 1000000000) (51116369 / 1000000000000) (25566159 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0265 :
    ∀ t ∈ Set.Icc ((757 / 32000) : ℝ) (303 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((104844959839 / 100000000000) : ℝ) ≤ Real.exp (2 * (757 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (757 / 32000)) (104844959839 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((303 / 12800) : ℝ)) ≤ (1048482362953 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (303 / 12800)) (1048482362953 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((370889817 / 200000000) : ℝ) ≤ Real.exp (3 * (329380087 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (329380087 / 100000000) / 16) (370889817 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3293904853 / 1000000000) : ℝ) / 16) ≤ (927242621 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3293904853 / 1000000000) / 16) (927242621 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((757 / 32000) : ℝ) (303 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (329380087 / 100000000) (3293904853 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (757 / 32000) (303 / 12800) (104844959839 / 100000000000) (1048482362953 / 1000000000000) (329380087 / 100000000) (3293904853 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (757 / 32000) (303 / 12800) (329380087 / 100000000) (3293904853 / 1000000000) (51100587 / 1000000000000) (12779133 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (329380087 / 100000000) (3293904853 / 1000000000) (370889817 / 200000000) (927242621 / 500000000) (51100587 / 1000000000000) (12779133 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0266 :
    ∀ t ∈ Set.Icc ((303 / 12800) : ℝ) (379 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((131060295369 / 125000000000) : ℝ) ≤ Real.exp (2 * (303 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (303 / 12800)) (131060295369 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((379 / 16000) : ℝ)) ≤ (1048515128539 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (379 / 16000)) (1048515128539 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((463621219 / 250000000) : ℝ) ≤ Real.exp (3 * (3293903803 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3293903803 / 1000000000) / 16) (463621219 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3294007789 / 1000000000) : ℝ) / 16) ≤ (370904207 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3294007789 / 1000000000) / 16) (370904207 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((303 / 12800) : ℝ) (379 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3293903803 / 1000000000) (3294007789 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (303 / 12800) (379 / 16000) (131060295369 / 125000000000) (1048515128539 / 1000000000000) (3293903803 / 1000000000) (3294007789 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (303 / 12800) (379 / 16000) (3293903803 / 1000000000) (3294007789 / 1000000000) (51084809 / 1000000000000) (204403 / 4000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3293903803 / 1000000000) (3294007789 / 1000000000) (463621219 / 250000000) (370904207 / 200000000) (51084809 / 1000000000000) (204403 / 4000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0267 :
    ∀ t ∈ Set.Icc ((379 / 16000) : ℝ) (1517 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((524257564269 / 500000000000) : ℝ) ≤ Real.exp (2 * (379 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (379 / 16000)) (524257564269 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1517 / 64000) : ℝ)) ≤ (1048547895149 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1517 / 64000)) (1048547895149 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1854520669 / 1000000000) : ℝ) ≤ Real.exp (3 * (3294006739 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3294006739 / 1000000000) / 16) (1854520669 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((411763841 / 125000000) : ℝ) / 16) ≤ (185455683 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (411763841 / 125000000) / 16) (185455683 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((379 / 16000) : ℝ) (1517 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3294006739 / 1000000000) (411763841 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (379 / 16000) (1517 / 64000) (524257564269 / 500000000000) (1048547895149 / 1000000000000) (3294006739 / 1000000000) (411763841 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (379 / 16000) (1517 / 64000) (3294006739 / 1000000000) (411763841 / 125000000) (12767259 / 250000000000) (12771243 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3294006739 / 1000000000) (411763841 / 125000000) (1854520669 / 1000000000) (185455683 / 100000000) (12767259 / 250000000000) (12771243 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0268 :
    ∀ t ∈ Set.Icc ((1517 / 64000) : ℝ) (759 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((262136973787 / 250000000000) : ℝ) ≤ Real.exp (2 * (1517 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1517 / 64000)) (262136973787 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((759 / 32000) : ℝ)) ≤ (524290331391 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (759 / 32000)) (524290331391 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((115909779 / 62500000) : ℝ) ≤ Real.exp (3 * (3294109679 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3294109679 / 1000000000) / 16) (115909779 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3294213671 / 1000000000) : ℝ) / 16) ≤ (927296313 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3294213671 / 1000000000) / 16) (927296313 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1517 / 64000) : ℝ) (759 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3294109679 / 1000000000) (3294213671 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1517 / 64000) (759 / 32000) (262136973787 / 250000000000) (524290331391 / 500000000000) (3294109679 / 1000000000) (3294213671 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1517 / 64000) (759 / 32000) (3294109679 / 1000000000) (3294213671 / 1000000000) (51053267 / 1000000000000) (25534599 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3294109679 / 1000000000) (3294213671 / 1000000000) (115909779 / 62500000) (927296313 / 500000000) (51053267 / 1000000000000) (25534599 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0269 :
    ∀ t ∈ Set.Icc ((759 / 32000) : ℝ) (1519 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1048580662781 / 1000000000000) : ℝ) ≤ Real.exp (2 * (759 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (759 / 32000)) (1048580662781 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1519 / 64000) : ℝ)) ≤ (13107667893 / 12500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1519 / 64000)) (13107667893 / 12500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((92729613 / 50000000) : ℝ) ≤ Real.exp (3 * (3294212621 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3294212621 / 1000000000) / 16) (92729613 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((411789577 / 125000000) : ℝ) / 16) ≤ (74185137 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (411789577 / 125000000) / 16) (74185137 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((759 / 32000) : ℝ) (1519 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3294212621 / 1000000000) (411789577 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (759 / 32000) (1519 / 64000) (1048580662781 / 1000000000000) (13107667893 / 12500000000) (3294212621 / 1000000000) (411789577 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (759 / 32000) (1519 / 64000) (3294212621 / 1000000000) (411789577 / 125000000) (25518751 / 500000000000) (51053429 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3294212621 / 1000000000) (411789577 / 125000000) (92729613 / 50000000) (74185137 / 40000000) (25518751 / 500000000000) (51053429 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0270 :
    ∀ t ∈ Set.Icc ((1519 / 64000) : ℝ) (19 / 800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1048613431439 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1519 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1519 / 64000)) (1048613431439 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((19 / 800) : ℝ)) ≤ (524323100561 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (19 / 800)) (524323100561 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1854628059 / 1000000000) : ℝ) ≤ Real.exp (3 * (3294315567 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3294315567 / 1000000000) / 16) (1854628059 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((658883913 / 200000000) : ℝ) / 16) ≤ (74186569 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (658883913 / 200000000) / 16) (74186569 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1519 / 64000) : ℝ) (19 / 800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3294315567 / 1000000000) (658883913 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1519 / 64000) (19 / 800) (1048613431439 / 1000000000000) (524323100561 / 500000000000) (3294315567 / 1000000000) (658883913 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1519 / 64000) (19 / 800) (3294315567 / 1000000000) (658883913 / 200000000) (25510871 / 500000000000) (1594927 / 31250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3294315567 / 1000000000) (658883913 / 200000000) (1854628059 / 1000000000) (74186569 / 40000000) (25510871 / 500000000000) (1594927 / 31250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0271 :
    ∀ t ∈ Set.Icc ((19 / 800) : ℝ) (1521 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1048646201121 / 1000000000000) : ℝ) ≤ Real.exp (2 * (19 / 800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (19 / 800)) (1048646201121 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1521 / 64000) : ℝ)) ≤ (262169742957 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1521 / 64000)) (262169742957 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1854663859 / 1000000000) : ℝ) ≤ Real.exp (3 * (823604629 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (823604629 / 250000000) / 16) (1854663859 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1647261259 / 500000000) : ℝ) / 16) ≤ (1854700027 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1647261259 / 500000000) / 16) (1854700027 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((19 / 800) : ℝ) (1521 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (823604629 / 250000000) (1647261259 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (19 / 800) (1521 / 64000) (1048646201121 / 1000000000000) (262169742957 / 250000000000) (823604629 / 250000000) (1647261259 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (19 / 800) (1521 / 64000) (823604629 / 250000000) (1647261259 / 500000000) (25502993 / 500000000000) (3188869 / 62500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (823604629 / 250000000) (1647261259 / 500000000) (1854663859 / 1000000000) (1854700027 / 1000000000) (25502993 / 500000000000) (3188869 / 62500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0272 :
    ∀ t ∈ Set.Icc ((1521 / 64000) : ℝ) (761 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1048678971827 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1521 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1521 / 64000)) (1048678971827 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((761 / 32000) : ℝ)) ≤ (524355871779 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (761 / 32000)) (524355871779 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1854699661 / 1000000000) : ℝ) ≤ Real.exp (3 * (823630367 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (823630367 / 250000000) / 16) (1854699661 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3294625473 / 1000000000) : ℝ) / 16) ≤ (185473583 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3294625473 / 1000000000) / 16) (185473583 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1521 / 64000) : ℝ) (761 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (823630367 / 250000000) (3294625473 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1521 / 64000) (761 / 32000) (1048678971827 / 1000000000000) (524355871779 / 500000000000) (823630367 / 250000000) (3294625473 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1521 / 64000) (761 / 32000) (823630367 / 250000000) (3294625473 / 1000000000) (25495117 / 500000000000) (12751537 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (823630367 / 250000000) (3294625473 / 1000000000) (1854699661 / 1000000000) (185473583 / 100000000) (25495117 / 500000000000) (12751537 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0273 :
    ∀ t ∈ Set.Icc ((761 / 32000) : ℝ) (1523 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1048711743557 / 1000000000000) : ℝ) ≤ Real.exp (2 * (761 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (761 / 32000)) (1048711743557 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1523 / 64000) : ℝ)) ≤ (131093064539 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1523 / 64000)) (131093064539 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((231841933 / 125000000) : ℝ) ≤ Real.exp (3 * (3294624423 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3294624423 / 1000000000) / 16) (231841933 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((205920527 / 62500000) : ℝ) / 16) ≤ (463692909 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (205920527 / 62500000) / 16) (463692909 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((761 / 32000) : ℝ) (1523 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3294624423 / 1000000000) (205920527 / 62500000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (761 / 32000) (1523 / 64000) (1048711743557 / 1000000000000) (131093064539 / 125000000000) (3294624423 / 1000000000) (205920527 / 62500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (761 / 32000) (1523 / 64000) (3294624423 / 1000000000) (205920527 / 62500000) (50974487 / 1000000000000) (12747599 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3294624423 / 1000000000) (205920527 / 62500000) (231841933 / 125000000) (463692909 / 250000000) (50974487 / 1000000000000) (12747599 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0274 :
    ∀ t ∈ Set.Icc ((1523 / 64000) : ℝ) (381 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1048744516311 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1523 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1523 / 64000)) (1048744516311 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((381 / 16000) : ℝ)) ≤ (104877729009 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (381 / 16000)) (104877729009 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((185477127 / 100000000) : ℝ) ≤ Real.exp (3 * (1647363691 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1647363691 / 500000000) / 16) (185477127 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1647415697 / 500000000) : ℝ) / 16) ≤ (463701861 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1647415697 / 500000000) / 16) (463701861 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1523 / 64000) : ℝ) (381 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1647363691 / 500000000) (1647415697 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1523 / 64000) (381 / 16000) (1048744516311 / 1000000000000) (104877729009 / 100000000000) (1647363691 / 500000000) (1647415697 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1523 / 64000) (381 / 16000) (1647363691 / 500000000) (1647415697 / 500000000) (6369843 / 125000000000) (50974649 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1647363691 / 500000000) (1647415697 / 500000000) (185477127 / 100000000) (463701861 / 250000000) (6369843 / 125000000000) (50974649 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0275 :
    ∀ t ∈ Set.Icc ((381 / 16000) : ℝ) (61 / 2560), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1048777290089 / 1000000000000) : ℝ) ≤ Real.exp (2 * (381 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (381 / 16000)) (1048777290089 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((61 / 2560) : ℝ)) ≤ (262202516223 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (61 / 2560)) (262202516223 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1854807077 / 1000000000) : ℝ) ≤ Real.exp (3 * (411853793 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (411853793 / 125000000) / 16) (1854807077 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3294934359 / 1000000000) : ℝ) / 16) ≤ (1854843253 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3294934359 / 1000000000) / 16) (1854843253 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((381 / 16000) : ℝ) (61 / 2560),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (411853793 / 125000000) (3294934359 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (381 / 16000) (61 / 2560) (1048777290089 / 1000000000000) (262202516223 / 250000000000) (411853793 / 125000000) (3294934359 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (381 / 16000) (61 / 2560) (411853793 / 125000000) (3294934359 / 1000000000) (10188601 / 200000000000) (25479453 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (411853793 / 125000000) (3294934359 / 1000000000) (1854807077 / 1000000000) (1854843253 / 1000000000) (10188601 / 200000000000) (25479453 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0276 :
    ∀ t ∈ Set.Icc ((61 / 2560) : ℝ) (763 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1048810064891 / 1000000000000) : ℝ) ≤ Real.exp (2 * (61 / 2560)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (61 / 2560)) (1048810064891 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((763 / 32000) : ℝ)) ≤ (1048842840719 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (763 / 32000)) (1048842840719 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((927421443 / 500000000) : ℝ) ≤ Real.exp (3 * (3294933309 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3294933309 / 1000000000) / 16) (927421443 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3295037327 / 1000000000) : ℝ) / 16) ≤ (231859883 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3295037327 / 1000000000) / 16) (231859883 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((61 / 2560) : ℝ) (763 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3294933309 / 1000000000) (3295037327 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (61 / 2560) (763 / 32000) (1048810064891 / 1000000000000) (1048842840719 / 1000000000000) (3294933309 / 1000000000) (3295037327 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (61 / 2560) (763 / 32000) (3294933309 / 1000000000) (3295037327 / 1000000000) (50927271 / 1000000000000) (795987 / 15625000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3294933309 / 1000000000) (3295037327 / 1000000000) (927421443 / 500000000) (231859883 / 125000000) (50927271 / 1000000000000) (795987 / 15625000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0277 :
    ∀ t ∈ Set.Icc ((763 / 32000) : ℝ) (1527 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((524421420359 / 500000000000) : ℝ) ≤ Real.exp (2 * (763 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (763 / 32000)) (524421420359 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1527 / 64000) : ℝ)) ≤ (104887561757 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1527 / 64000)) (104887561757 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1854878697 / 1000000000) : ℝ) ≤ Real.exp (3 * (3295036277 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3295036277 / 1000000000) / 16) (1854878697 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3295140299 / 1000000000) : ℝ) / 16) ≤ (1854914877 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3295140299 / 1000000000) / 16) (1854914877 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((763 / 32000) : ℝ) (1527 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3295036277 / 1000000000) (3295140299 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (763 / 32000) (1527 / 64000) (524421420359 / 500000000000) (104887561757 / 100000000000) (3295036277 / 1000000000) (3295140299 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (763 / 32000) (1527 / 64000) (3295036277 / 1000000000) (3295140299 / 1000000000) (50911541 / 1000000000000) (50927433 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3295036277 / 1000000000) (3295140299 / 1000000000) (1854878697 / 1000000000) (1854914877 / 1000000000) (50911541 / 1000000000000) (50927433 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0278 :
    ∀ t ∈ Set.Icc ((1527 / 64000) : ℝ) (191 / 8000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1048875617569 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1527 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1527 / 64000)) (1048875617569 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((191 / 8000) : ℝ)) ≤ (209781679089 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (191 / 8000)) (209781679089 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((185491451 / 100000000) : ℝ) ≤ Real.exp (3 * (3295139249 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3295139249 / 1000000000) / 16) (185491451 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3295243273 / 1000000000) : ℝ) / 16) ≤ (1854950691 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3295243273 / 1000000000) / 16) (1854950691 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1527 / 64000) : ℝ) (191 / 8000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3295139249 / 1000000000) (3295243273 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1527 / 64000) (191 / 8000) (1048875617569 / 1000000000000) (209781679089 / 200000000000) (3295139249 / 1000000000) (3295243273 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1527 / 64000) (191 / 8000) (3295139249 / 1000000000) (3295243273 / 1000000000) (6361977 / 125000000000) (50911703 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3295139249 / 1000000000) (3295243273 / 1000000000) (185491451 / 100000000) (1854950691 / 1000000000) (6361977 / 125000000000) (50911703 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0279 :
    ∀ t ∈ Set.Icc ((191 / 8000) : ℝ) (1529 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((262227098861 / 250000000000) : ℝ) ≤ Real.exp (2 * (191 / 8000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (191 / 8000)) (262227098861 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1529 / 64000) : ℝ)) ≤ (209788234869 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1529 / 64000)) (209788234869 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((74198013 / 40000000) : ℝ) ≤ Real.exp (3 * (3295242223 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3295242223 / 1000000000) / 16) (74198013 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3295346251 / 1000000000) : ℝ) / 16) ≤ (1854986507 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3295346251 / 1000000000) / 16) (1854986507 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((191 / 8000) : ℝ) (1529 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3295242223 / 1000000000) (3295346251 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (191 / 8000) (1529 / 64000) (262227098861 / 250000000000) (209788234869 / 200000000000) (3295242223 / 1000000000) (3295346251 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (191 / 8000) (1529 / 64000) (3295242223 / 1000000000) (3295346251 / 1000000000) (10176019 / 200000000000) (25447989 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3295242223 / 1000000000) (3295346251 / 1000000000) (74198013 / 40000000) (1854986507 / 1000000000) (10176019 / 200000000000) (25447989 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch013 :
    ∀ t ∈ Set.Icc ((1509 / 64000) : ℝ) (1529 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0260
      hpThetaDensityTwoTermCompact_cell0261)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0262
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0263
      hpThetaDensityTwoTermCompact_cell0264)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0265
      hpThetaDensityTwoTermCompact_cell0266)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0267
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0268
      hpThetaDensityTwoTermCompact_cell0269))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0270
      hpThetaDensityTwoTermCompact_cell0271)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0272
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0273
      hpThetaDensityTwoTermCompact_cell0274)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0275
      hpThetaDensityTwoTermCompact_cell0276)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0277
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0278
      hpThetaDensityTwoTermCompact_cell0279)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch013
end HodgeProofHP
