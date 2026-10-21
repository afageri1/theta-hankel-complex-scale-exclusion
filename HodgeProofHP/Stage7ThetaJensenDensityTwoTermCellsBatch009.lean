/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0180 :
    ∀ t ∈ Set.Icc ((1429 / 64000) : ℝ) (143 / 6400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((522834174813 / 500000000000) : ℝ) ≤ Real.exp (2 * (1429 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1429 / 64000)) (522834174813 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((143 / 6400) : ℝ)) ≤ (1045701027273 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (143 / 6400)) (1045701027273 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((925706723 / 500000000) : ℝ) ≤ Real.exp (3 * (3285063321 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3285063321 / 1000000000) / 16) (925706723 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((821291757 / 250000000) : ℝ) / 16) ≤ (1851449449 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (821291757 / 250000000) / 16) (1851449449 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1429 / 64000) : ℝ) (143 / 6400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3285063321 / 1000000000) (821291757 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1429 / 64000) (143 / 6400) (522834174813 / 500000000000) (1045701027273 / 1000000000000) (3285063321 / 1000000000) (821291757 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1429 / 64000) (143 / 6400) (3285063321 / 1000000000) (821291757 / 250000000) (26228911 / 500000000000) (52474147 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3285063321 / 1000000000) (821291757 / 250000000) (925706723 / 500000000) (1851449449 / 1000000000) (26228911 / 500000000000) (52474147 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0181 :
    ∀ t ∈ Set.Icc ((143 / 6400) : ℝ) (1431 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((130712628409 / 125000000000) : ℝ) ≤ Real.exp (2 * (143 / 6400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (143 / 6400)) (130712628409 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1431 / 64000) : ℝ)) ≤ (1045733705941 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1431 / 64000)) (1045733705941 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((462862271 / 250000000) : ℝ) ≤ Real.exp (3 * (3285165981 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3285165981 / 1000000000) / 16) (462862271 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3285269691 / 1000000000) : ℝ) / 16) ≤ (57858909 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3285269691 / 1000000000) / 16) (57858909 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((143 / 6400) : ℝ) (1431 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3285165981 / 1000000000) (3285269691 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (143 / 6400) (1431 / 64000) (130712628409 / 125000000000) (1045733705941 / 1000000000000) (3285165981 / 1000000000) (3285269691 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (143 / 6400) (1431 / 64000) (3285165981 / 1000000000) (3285269691 / 1000000000) (13110417 / 250000000000) (13114497 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3285165981 / 1000000000) (3285269691 / 1000000000) (462862271 / 250000000) (57858909 / 31250000) (13110417 / 250000000000) (13114497 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0182 :
    ∀ t ∈ Set.Icc ((1431 / 64000) : ℝ) (179 / 8000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((52286685297 / 50000000000) : ℝ) ≤ Real.exp (2 * (1431 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1431 / 64000)) (52286685297 / 50000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((179 / 8000) : ℝ)) ≤ (104576638563 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (179 / 8000)) (104576638563 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((462871181 / 250000000) : ℝ) ≤ Real.exp (3 * (821317161 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (821317161 / 250000000) / 16) (462871181 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3285372357 / 1000000000) : ℝ) / 16) ≤ (1851520729 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3285372357 / 1000000000) / 16) (1851520729 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1431 / 64000) : ℝ) (179 / 8000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (821317161 / 250000000) (3285372357 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1431 / 64000) (179 / 8000) (52286685297 / 50000000000) (104576638563 / 100000000000) (821317161 / 250000000) (3285372357 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1431 / 64000) (179 / 8000) (821317161 / 250000000) (3285372357 / 1000000000) (52425519 / 1000000000000) (26220917 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (821317161 / 250000000) (3285372357 / 1000000000) (462871181 / 250000000) (1851520729 / 1000000000) (52425519 / 1000000000000) (26220917 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0183 :
    ∀ t ∈ Set.Icc ((179 / 8000) : ℝ) (1433 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1045766385629 / 1000000000000) : ℝ) ≤ Real.exp (2 * (179 / 8000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (179 / 8000)) (1045766385629 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1433 / 64000) : ℝ)) ≤ (52289953317 / 50000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1433 / 64000)) (52289953317 / 50000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((370304073 / 200000000) : ℝ) ≤ Real.exp (3 * (328537131 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (328537131 / 100000000) / 16) (370304073 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3285475027 / 1000000000) : ℝ) / 16) ≤ (462889093 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3285475027 / 1000000000) / 16) (462889093 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((179 / 8000) : ℝ) (1433 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (328537131 / 100000000) (3285475027 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (179 / 8000) (1433 / 64000) (1045766385629 / 1000000000000) (52289953317 / 50000000000) (328537131 / 100000000) (3285475027 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (179 / 8000) (1433 / 64000) (328537131 / 100000000) (3285475027 / 1000000000) (26204687 / 500000000000) (10485137 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (328537131 / 100000000) (3285475027 / 1000000000) (370304073 / 200000000) (462889093 / 250000000) (26204687 / 500000000000) (10485137 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0184 :
    ∀ t ∈ Set.Icc ((1433 / 64000) : ℝ) (717 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1045799066339 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1433 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1433 / 64000)) (1045799066339 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((717 / 32000) : ℝ)) ≤ (130728968509 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (717 / 32000)) (130728968509 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((231444501 / 125000000) : ℝ) ≤ Real.exp (3 * (164273699 / 50000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (164273699 / 50000000) / 16) (231444501 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3285577699 / 1000000000) : ℝ) / 16) ≤ (1851592017 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3285577699 / 1000000000) / 16) (1851592017 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1433 / 64000) : ℝ) (717 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (164273699 / 50000000) (3285577699 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1433 / 64000) (717 / 32000) (1045799066339 / 1000000000000) (130728968509 / 125000000000) (164273699 / 50000000) (3285577699 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1433 / 64000) (717 / 32000) (164273699 / 50000000) (3285577699 / 1000000000) (52393233 / 1000000000000) (2620477 / 50000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (164273699 / 50000000) (3285577699 / 1000000000) (231444501 / 125000000) (1851592017 / 1000000000) (52393233 / 1000000000000) (2620477 / 50000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0185 :
    ∀ t ∈ Set.Icc ((717 / 32000) : ℝ) (287 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1045831748071 / 1000000000000) : ℝ) ≤ Real.exp (2 * (717 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (717 / 32000)) (1045831748071 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((287 / 12800) : ℝ)) ≤ (130733053853 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (287 / 12800)) (130733053853 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1851591653 / 1000000000) : ℝ) ≤ Real.exp (3 * (3285576653 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3285576653 / 1000000000) / 16) (1851591653 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((26285443 / 8000000) : ℝ) / 16) ≤ (115726729 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (26285443 / 8000000) / 16) (115726729 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((717 / 32000) : ℝ) (287 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3285576653 / 1000000000) (26285443 / 8000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (717 / 32000) (287 / 12800) (1045831748071 / 1000000000000) (130733053853 / 125000000000) (3285576653 / 1000000000) (26285443 / 8000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (717 / 32000) (287 / 12800) (3285576653 / 1000000000) (26285443 / 8000000) (52377097 / 1000000000000) (52393399 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3285576653 / 1000000000) (26285443 / 8000000) (1851591653 / 1000000000) (115726729 / 62500000) (52377097 / 1000000000000) (52393399 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0186 :
    ∀ t ∈ Set.Icc ((287 / 12800) : ℝ) (359 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1045864430823 / 1000000000000) : ℝ) ≤ Real.exp (2 * (287 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (287 / 12800)) (1045864430823 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((359 / 16000) : ℝ)) ≤ (522948557299 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (359 / 16000)) (522948557299 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1851627299 / 1000000000) : ℝ) ≤ Real.exp (3 * (102677479 / 31250000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (102677479 / 31250000) / 16) (1851627299 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1642891527 / 500000000) : ℝ) / 16) ≤ (115728957 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1642891527 / 500000000) / 16) (115728957 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((287 / 12800) : ℝ) (359 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (102677479 / 31250000) (1642891527 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (287 / 12800) (359 / 16000) (1045864430823 / 1000000000000) (522948557299 / 500000000000) (102677479 / 31250000) (1642891527 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (287 / 12800) (359 / 16000) (102677479 / 31250000) (1642891527 / 500000000) (26180483 / 500000000000) (52377263 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (102677479 / 31250000) (1642891527 / 500000000) (1851627299 / 1000000000) (115728957 / 62500000) (26180483 / 500000000000) (52377263 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0187 :
    ∀ t ∈ Set.Icc ((359 / 16000) : ℝ) (1437 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1045897114597 / 1000000000000) : ℝ) ≤ Real.exp (2 * (359 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (359 / 16000)) (1045897114597 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1437 / 64000) : ℝ)) ≤ (522964899697 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1437 / 64000)) (522964899697 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((462915737 / 250000000) : ℝ) ≤ Real.exp (3 * (410722751 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (410722751 / 125000000) / 16) (462915737 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3285885737 / 1000000000) : ℝ) / 16) ≤ (1851698963 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3285885737 / 1000000000) / 16) (1851698963 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((359 / 16000) : ℝ) (1437 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (410722751 / 125000000) (3285885737 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (359 / 16000) (1437 / 64000) (1045897114597 / 1000000000000) (522964899697 / 500000000000) (410722751 / 125000000) (3285885737 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (359 / 16000) (1437 / 64000) (410722751 / 125000000) (3285885737 / 1000000000) (26172419 / 500000000000) (52361131 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (410722751 / 125000000) (3285885737 / 1000000000) (462915737 / 250000000) (1851698963 / 1000000000) (26172419 / 500000000000) (52361131 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0188 :
    ∀ t ∈ Set.Icc ((1437 / 64000) : ℝ) (719 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1045929799393 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1437 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1437 / 64000)) (1045929799393 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((719 / 32000) : ℝ)) ≤ (1045962485211 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (719 / 32000)) (1045962485211 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((925849299 / 500000000) : ℝ) ≤ Real.exp (3 * (328588469 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (328588469 / 100000000) / 16) (925849299 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1642994211 / 500000000) : ℝ) / 16) ≤ (370346923 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1642994211 / 500000000) / 16) (370346923 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1437 / 64000) : ℝ) (719 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (328588469 / 100000000) (1642994211 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1437 / 64000) (719 / 32000) (1045929799393 / 1000000000000) (1045962485211 / 1000000000000) (328588469 / 100000000) (1642994211 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1437 / 64000) (719 / 32000) (328588469 / 100000000) (1642994211 / 500000000) (13082179 / 250000000000) (13086251 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (328588469 / 100000000) (1642994211 / 500000000) (925849299 / 500000000) (370346923 / 200000000) (13082179 / 250000000000) (13086251 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0189 :
    ∀ t ∈ Set.Icc ((719 / 32000) : ℝ) (1439 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((104596248521 / 100000000000) : ℝ) ≤ Real.exp (2 * (719 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (719 / 32000)) (104596248521 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1439 / 64000) : ℝ)) ≤ (1045995172049 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1439 / 64000)) (1045995172049 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((7406937 / 4000000) : ℝ) ≤ Real.exp (3 * (26287899 / 8000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (26287899 / 8000000) / 16) (7406937 / 4000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3286091111 / 1000000000) : ℝ) / 16) ≤ (1851770269 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3286091111 / 1000000000) / 16) (1851770269 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((719 / 32000) : ℝ) (1439 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (26287899 / 8000000) (3286091111 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (719 / 32000) (1439 / 64000) (104596248521 / 100000000000) (1045995172049 / 1000000000000) (26287899 / 8000000) (3286091111 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (719 / 32000) (1439 / 64000) (26287899 / 8000000) (3286091111 / 1000000000) (52312597 / 1000000000000) (26164441 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (26287899 / 8000000) (3286091111 / 1000000000) (7406937 / 4000000) (1851770269 / 1000000000) (52312597 / 1000000000000) (26164441 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0190 :
    ∀ t ∈ Set.Icc ((1439 / 64000) : ℝ) (9 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((65374698253 / 62500000000) : ℝ) ≤ Real.exp (2 * (1439 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1439 / 64000)) (65374698253 / 62500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9 / 400) : ℝ)) ≤ (1046027859909 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9 / 400)) (1046027859909 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((115735619 / 62500000) : ℝ) ≤ Real.exp (3 * (205380629 / 62500000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (205380629 / 62500000) / 16) (115735619 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3286193803 / 1000000000) : ℝ) / 16) ≤ (462951481 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3286193803 / 1000000000) / 16) (462951481 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1439 / 64000) : ℝ) (9 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (205380629 / 62500000) (3286193803 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1439 / 64000) (9 / 400) (65374698253 / 62500000000) (1046027859909 / 1000000000000) (205380629 / 62500000) (3286193803 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1439 / 64000) (9 / 400) (205380629 / 62500000) (3286193803 / 1000000000) (13074121 / 250000000000) (52312763 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (205380629 / 62500000) (3286193803 / 1000000000) (115735619 / 62500000) (462951481 / 250000000) (13074121 / 250000000000) (52312763 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0191 :
    ∀ t ∈ Set.Icc ((9 / 400) : ℝ) (1441 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((261506964977 / 250000000000) : ℝ) ≤ Real.exp (2 * (9 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9 / 400)) (261506964977 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1441 / 64000) : ℝ)) ≤ (1046060548791 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1441 / 64000)) (1046060548791 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((46295139 / 25000000) : ℝ) ≤ Real.exp (3 * (821548189 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (821548189 / 250000000) / 16) (46295139 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1643148249 / 500000000) : ℝ) / 16) ≤ (925920791 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1643148249 / 500000000) / 16) (925920791 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9 / 400) : ℝ) (1441 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (821548189 / 250000000) (1643148249 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (9 / 400) (1441 / 64000) (261506964977 / 250000000000) (1046060548791 / 1000000000000) (821548189 / 250000000) (1643148249 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (9 / 400) (1441 / 64000) (821548189 / 250000000) (1643148249 / 500000000) (26140187 / 500000000000) (52296649 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (821548189 / 250000000) (1643148249 / 500000000) (46295139 / 25000000) (925920791 / 500000000) (26140187 / 500000000000) (52296649 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0192 :
    ∀ t ∈ Set.Icc ((1441 / 64000) : ℝ) (721 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((104606054879 / 100000000000) : ℝ) ≤ Real.exp (2 * (1441 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1441 / 64000)) (104606054879 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((721 / 32000) : ℝ)) ≤ (523046619347 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (721 / 32000)) (523046619347 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1851841217 / 1000000000) : ℝ) ≤ Real.exp (3 * (3286295451 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3286295451 / 1000000000) / 16) (1851841217 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3286399197 / 1000000000) : ℝ) / 16) ≤ (1851877241 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3286399197 / 1000000000) / 16) (1851877241 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1441 / 64000) : ℝ) (721 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3286295451 / 1000000000) (3286399197 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1441 / 64000) (721 / 32000) (104606054879 / 100000000000) (523046619347 / 500000000000) (3286295451 / 1000000000) (3286399197 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1441 / 64000) (721 / 32000) (3286295451 / 1000000000) (3286399197 / 1000000000) (5226427 / 100000000000) (2614027 / 50000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3286295451 / 1000000000) (3286399197 / 1000000000) (1851841217 / 1000000000) (1851877241 / 1000000000) (5226427 / 100000000000) (2614027 / 50000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0193 :
    ∀ t ∈ Set.Icc ((721 / 32000) : ℝ) (1443 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1046093238693 / 1000000000000) : ℝ) ≤ Real.exp (2 * (721 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (721 / 32000)) (1046093238693 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1443 / 64000) : ℝ)) ≤ (523062964809 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1443 / 64000)) (523062964809 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1851876877 / 1000000000) : ℝ) ≤ Real.exp (3 * (3286398149 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3286398149 / 1000000000) / 16) (1851876877 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1643250949 / 500000000) : ℝ) / 16) ≤ (925956451 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1643250949 / 500000000) / 16) (925956451 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((721 / 32000) : ℝ) (1443 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3286398149 / 1000000000) (1643250949 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (721 / 32000) (1443 / 64000) (1046093238693 / 1000000000000) (523062964809 / 500000000000) (3286398149 / 1000000000) (1643250949 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (721 / 32000) (1443 / 64000) (3286398149 / 1000000000) (1643250949 / 500000000) (52248169 / 1000000000000) (10452887 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3286398149 / 1000000000) (1643250949 / 500000000) (1851876877 / 1000000000) (925956451 / 500000000) (52248169 / 1000000000000) (10452887 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0194 :
    ∀ t ∈ Set.Icc ((1443 / 64000) : ℝ) (361 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1046125929617 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1443 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1443 / 64000)) (1046125929617 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((361 / 16000) : ℝ)) ≤ (261539655391 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (361 / 16000)) (261539655391 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((925956269 / 500000000) : ℝ) ≤ Real.exp (3 * (3286500851 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3286500851 / 1000000000) / 16) (925956269 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3286604603 / 1000000000) : ℝ) / 16) ≤ (370389713 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3286604603 / 1000000000) / 16) (370389713 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1443 / 64000) : ℝ) (361 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3286500851 / 1000000000) (3286604603 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1443 / 64000) (361 / 16000) (1046125929617 / 1000000000000) (261539655391 / 250000000000) (3286500851 / 1000000000) (3286604603 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1443 / 64000) (361 / 16000) (3286500851 / 1000000000) (3286604603 / 1000000000) (52232073 / 1000000000000) (10449667 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3286500851 / 1000000000) (3286604603 / 1000000000) (925956269 / 500000000) (370389713 / 200000000) (52232073 / 1000000000000) (10449667 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0195 :
    ∀ t ∈ Set.Icc ((361 / 16000) : ℝ) (289 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1046158621563 / 1000000000000) : ℝ) ≤ Real.exp (2 * (361 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (361 / 16000)) (1046158621563 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((289 / 12800) : ℝ)) ≤ (261547828633 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (289 / 12800)) (261547828633 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1851948201 / 1000000000) : ℝ) ≤ Real.exp (3 * (821650889 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (821650889 / 250000000) / 16) (1851948201 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3286707311 / 1000000000) : ℝ) / 16) ≤ (185198423 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3286707311 / 1000000000) / 16) (185198423 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((361 / 16000) : ℝ) (289 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (821650889 / 250000000) (3286707311 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (361 / 16000) (289 / 12800) (1046158621563 / 1000000000000) (261547828633 / 250000000000) (821650889 / 250000000) (3286707311 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (361 / 16000) (289 / 12800) (821650889 / 250000000) (3286707311 / 1000000000) (26107991 / 500000000000) (52232239 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (821650889 / 250000000) (3286707311 / 1000000000) (1851948201 / 1000000000) (185198423 / 100000000) (26107991 / 500000000000) (52232239 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0196 :
    ∀ t ∈ Set.Icc ((289 / 12800) : ℝ) (723 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1046191314531 / 1000000000000) : ℝ) ≤ Real.exp (2 * (289 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (289 / 12800)) (1046191314531 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((723 / 32000) : ℝ)) ≤ (1046224008521 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (723 / 32000)) (1046224008521 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((370396773 / 200000000) : ℝ) ≤ Real.exp (3 * (410838283 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (410838283 / 125000000) / 16) (370396773 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1643405011 / 500000000) : ℝ) / 16) ≤ (231502487 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1643405011 / 500000000) / 16) (231502487 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((289 / 12800) : ℝ) (723 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (410838283 / 125000000) (1643405011 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (289 / 12800) (723 / 32000) (1046191314531 / 1000000000000) (1046224008521 / 1000000000000) (410838283 / 125000000) (1643405011 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (289 / 12800) (723 / 32000) (410838283 / 125000000) (1643405011 / 500000000) (10439979 / 200000000000) (52216147 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (410838283 / 125000000) (1643405011 / 500000000) (370396773 / 200000000) (231502487 / 125000000) (10439979 / 200000000000) (52216147 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0197 :
    ∀ t ∈ Set.Icc ((723 / 32000) : ℝ) (1447 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((26155600213 / 25000000000) : ℝ) ≤ Real.exp (2 * (723 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (723 / 32000)) (26155600213 / 25000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1447 / 64000) : ℝ)) ≤ (261564175883 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1447 / 64000)) (261564175883 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((463004883 / 250000000) : ℝ) ≤ Real.exp (3 * (131472359 / 40000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (131472359 / 40000000) / 16) (463004883 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3286912737 / 1000000000) : ℝ) / 16) ≤ (370411113 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3286912737 / 1000000000) / 16) (370411113 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((723 / 32000) : ℝ) (1447 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (131472359 / 40000000) (3286912737 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (723 / 32000) (1447 / 64000) (26155600213 / 25000000000) (261564175883 / 250000000000) (131472359 / 40000000) (3286912737 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (723 / 32000) (1447 / 64000) (131472359 / 40000000) (3286912737 / 1000000000) (13045953 / 250000000000) (2610003 / 50000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (131472359 / 40000000) (3286912737 / 1000000000) (463004883 / 250000000) (370411113 / 200000000) (13045953 / 250000000000) (2610003 / 50000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0198 :
    ∀ t ∈ Set.Icc ((1447 / 64000) : ℝ) (181 / 8000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1046256703531 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1447 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1447 / 64000)) (1046256703531 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((181 / 8000) : ℝ)) ≤ (209257879913 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (181 / 8000)) (209257879913 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((2315069 / 1250000) : ℝ) ≤ Real.exp (3 * (3286911689 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3286911689 / 1000000000) / 16) (2315069 / 1250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1643507727 / 500000000) : ℝ) / 16) ≤ (370418247 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1643507727 / 500000000) / 16) (370418247 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1447 / 64000) : ℝ) (181 / 8000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3286911689 / 1000000000) (1643507727 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1447 / 64000) (181 / 8000) (1046256703531 / 1000000000000) (209257879913 / 200000000000) (3286911689 / 1000000000) (1643507727 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1447 / 64000) (181 / 8000) (3286911689 / 1000000000) (1643507727 / 500000000) (26083867 / 500000000000) (26091989 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3286911689 / 1000000000) (1643507727 / 500000000) (2315069 / 1250000) (370418247 / 200000000) (26083867 / 500000000000) (26091989 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0199 :
    ∀ t ∈ Set.Icc ((181 / 8000) : ℝ) (1449 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((261572349891 / 250000000000) : ℝ) ≤ Real.exp (2 * (181 / 8000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (181 / 8000)) (261572349891 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1449 / 64000) : ℝ)) ≤ (52316104831 / 50000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1449 / 64000)) (52316104831 / 50000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((185209087 / 100000000) : ℝ) ≤ Real.exp (3 * (3287014407 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3287014407 / 1000000000) / 16) (185209087 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((131484727 / 40000000) : ℝ) / 16) ≤ (1852126907 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (131484727 / 40000000) / 16) (1852126907 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((181 / 8000) : ℝ) (1449 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3287014407 / 1000000000) (131484727 / 40000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (181 / 8000) (1449 / 64000) (261572349891 / 250000000000) (52316104831 / 50000000000) (3287014407 / 1000000000) (131484727 / 40000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (181 / 8000) (1449 / 64000) (3287014407 / 1000000000) (131484727 / 40000000) (2607583 / 50000000000) (52167899 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3287014407 / 1000000000) (131484727 / 40000000) (185209087 / 100000000) (1852126907 / 1000000000) (2607583 / 50000000000) (52167899 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch009 :
    ∀ t ∈ Set.Icc ((1429 / 64000) : ℝ) (1449 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0180
      hpThetaDensityTwoTermCompact_cell0181)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0182
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0183
      hpThetaDensityTwoTermCompact_cell0184)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0185
      hpThetaDensityTwoTermCompact_cell0186)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0187
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0188
      hpThetaDensityTwoTermCompact_cell0189))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0190
      hpThetaDensityTwoTermCompact_cell0191)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0192
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0193
      hpThetaDensityTwoTermCompact_cell0194)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0195
      hpThetaDensityTwoTermCompact_cell0196)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0197
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0198
      hpThetaDensityTwoTermCompact_cell0199)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch009
end HodgeProofHP
