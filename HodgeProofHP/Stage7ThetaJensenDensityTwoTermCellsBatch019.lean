/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0380 :
    ∀ t ∈ Set.Icc ((1629 / 64000) : ℝ) (163 / 6400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((263056060659 / 250000000000) : ℝ) ≤ Real.exp (2 * (1629 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1629 / 64000)) (263056060659 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((163 / 6400) : ℝ)) ≤ (526128562579 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (163 / 6400)) (526128562579 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((371715389 / 200000000) : ℝ) ≤ Real.exp (3 * (1652829631 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1652829631 / 500000000) / 16) (371715389 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3305763619 / 1000000000) : ℝ) / 16) ≤ (1858613313 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3305763619 / 1000000000) / 16) (1858613313 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1629 / 64000) : ℝ) (163 / 6400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1652829631 / 500000000) (3305763619 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1629 / 64000) (163 / 6400) (263056060659 / 250000000000) (526128562579 / 500000000000) (1652829631 / 500000000) (3305763619 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1629 / 64000) (163 / 6400) (1652829631 / 500000000) (3305763619 / 1000000000) (1972583 / 40000000000) (24665009 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1652829631 / 500000000) (3305763619 / 1000000000) (371715389 / 200000000) (1858613313 / 1000000000) (1972583 / 40000000000) (24665009 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0381 :
    ∀ t ∈ Set.Icc ((163 / 6400) : ℝ) (1631 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1052257125157 / 1000000000000) : ℝ) ≤ Real.exp (2 * (163 / 6400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (163 / 6400)) (1052257125157 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1631 / 64000) : ℝ)) ≤ (1052290008707 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1631 / 64000)) (1052290008707 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((371722589 / 200000000) : ℝ) ≤ Real.exp (3 * (1652881283 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1652881283 / 500000000) / 16) (371722589 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1652933463 / 500000000) : ℝ) / 16) ≤ (929324657 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1652933463 / 500000000) / 16) (929324657 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((163 / 6400) : ℝ) (1631 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1652881283 / 500000000) (1652933463 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (163 / 6400) (1631 / 64000) (1052257125157 / 1000000000000) (1052290008707 / 1000000000000) (1652881283 / 500000000) (1652933463 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (163 / 6400) (1631 / 64000) (1652881283 / 500000000) (1652933463 / 500000000) (24649647 / 500000000000) (49314733 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1652881283 / 500000000) (1652933463 / 500000000) (371722589 / 200000000) (929324657 / 500000000) (24649647 / 500000000000) (49314733 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0382 :
    ∀ t ∈ Set.Icc ((1631 / 64000) : ℝ) (51 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((526145004353 / 500000000000) : ℝ) ≤ Real.exp (2 * (1631 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1631 / 64000)) (526145004353 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((51 / 2000) : ℝ)) ≤ (263080723321 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (51 / 2000)) (263080723321 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((929324473 / 500000000) : ℝ) ≤ Real.exp (3 * (3305865873 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3305865873 / 1000000000) / 16) (929324473 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((826492559 / 250000000) : ℝ) / 16) ≤ (929342659 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (826492559 / 250000000) / 16) (929342659 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1631 / 64000) : ℝ) (51 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3305865873 / 1000000000) (826492559 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1631 / 64000) (51 / 2000) (526145004353 / 500000000000) (263080723321 / 250000000000) (3305865873 / 1000000000) (826492559 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1631 / 64000) (51 / 2000) (3305865873 / 1000000000) (826492559 / 250000000) (49284017 / 1000000000000) (12324863 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3305865873 / 1000000000) (826492559 / 250000000) (929324473 / 500000000) (929342659 / 500000000) (49284017 / 1000000000000) (12324863 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0383 :
    ∀ t ∈ Set.Icc ((51 / 2000) : ℝ) (1633 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1052322893283 / 1000000000000) : ℝ) ≤ Real.exp (2 * (51 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (51 / 2000)) (1052322893283 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1633 / 64000) : ℝ)) ≤ (131544472361 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1633 / 64000)) (131544472361 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((37173699 / 20000000) : ℝ) ≤ Real.exp (3 * (1652984591 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1652984591 / 500000000) / 16) (37173699 / 20000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3306073549 / 1000000000) : ℝ) / 16) ≤ (1858721323 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3306073549 / 1000000000) / 16) (1858721323 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((51 / 2000) : ℝ) (1633 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1652984591 / 500000000) (3306073549 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (51 / 2000) (1633 / 64000) (1052322893283 / 1000000000000) (131544472361 / 125000000000) (1652984591 / 500000000) (3306073549 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (51 / 2000) (1633 / 64000) (1652984591 / 500000000) (3306073549 / 1000000000) (9853749 / 200000000000) (24642087 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1652984591 / 500000000) (3306073549 / 1000000000) (37173699 / 20000000) (1858721323 / 1000000000) (9853749 / 200000000000) (24642087 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0384 :
    ∀ t ∈ Set.Icc ((1633 / 64000) : ℝ) (817 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1052355778887 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1633 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1633 / 64000)) (1052355778887 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((817 / 32000) : ℝ)) ≤ (13154858319 / 12500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (817 / 32000)) (13154858319 / 12500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((371744191 / 200000000) : ℝ) ≤ Real.exp (3 * (206629531 / 62500000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (206629531 / 62500000) / 16) (371744191 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((661235373 / 200000000) : ℝ) / 16) ≤ (185875733 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (661235373 / 200000000) / 16) (185875733 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1633 / 64000) : ℝ) (817 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (206629531 / 62500000) (661235373 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1633 / 64000) (817 / 32000) (1052355778887 / 1000000000000) (13154858319 / 12500000000) (206629531 / 62500000) (661235373 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1633 / 64000) (817 / 32000) (206629531 / 62500000) (661235373 / 200000000) (12313369 / 250000000000) (24634451 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (206629531 / 62500000) (661235373 / 200000000) (371744191 / 200000000) (185875733 / 100000000) (12313369 / 250000000000) (24634451 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0385 :
    ∀ t ∈ Set.Icc ((817 / 32000) : ℝ) (327 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1052388665519 / 1000000000000) : ℝ) ≤ Real.exp (2 * (817 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (817 / 32000)) (1052388665519 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((327 / 12800) : ℝ)) ≤ (52621077659 / 50000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (327 / 12800)) (52621077659 / 50000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((929378481 / 500000000) : ℝ) ≤ Real.exp (3 * (826543953 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (826543953 / 250000000) / 16) (929378481 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((661256037 / 200000000) : ℝ) / 16) ≤ (1858793339 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (661256037 / 200000000) / 16) (1858793339 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((817 / 32000) : ℝ) (327 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (826543953 / 250000000) (661256037 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (817 / 32000) (327 / 12800) (1052388665519 / 1000000000000) (52621077659 / 50000000000) (826543953 / 250000000) (661256037 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (817 / 32000) (327 / 12800) (826543953 / 250000000) (661256037 / 200000000) (12309553 / 250000000000) (49253633 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (826543953 / 250000000) (661256037 / 200000000) (929378481 / 500000000) (1858793339 / 1000000000) (12309553 / 250000000000) (49253633 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0386 :
    ∀ t ∈ Set.Icc ((327 / 12800) : ℝ) (409 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1052421553179 / 1000000000000) : ℝ) ≤ Real.exp (2 * (327 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (327 / 12800)) (1052421553179 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((409 / 16000) : ℝ)) ≤ (1052454441867 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (409 / 16000)) (1052454441867 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1858792971 / 1000000000) : ℝ) ≤ Real.exp (3 * (826569783 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (826569783 / 250000000) / 16) (1858792971 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((826595877 / 250000000) : ℝ) / 16) ≤ (37176587 / 20000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (826595877 / 250000000) / 16) (37176587 / 20000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((327 / 12800) : ℝ) (409 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (826569783 / 250000000) (826595877 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (327 / 12800) (409 / 16000) (1052421553179 / 1000000000000) (1052454441867 / 1000000000000) (826569783 / 250000000) (826595877 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (327 / 12800) (409 / 16000) (826569783 / 250000000) (826595877 / 250000000) (6152869 / 125000000000) (49238369 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (826569783 / 250000000) (826595877 / 250000000) (1858792971 / 1000000000) (37176587 / 20000000) (6152869 / 125000000000) (49238369 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0387 :
    ∀ t ∈ Set.Icc ((409 / 16000) : ℝ) (1637 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((526227220933 / 500000000000) : ℝ) ≤ Real.exp (2 * (409 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (409 / 16000)) (526227220933 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1637 / 64000) : ℝ)) ≤ (526243665791 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1637 / 64000)) (526243665791 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((929414491 / 500000000) : ℝ) ≤ Real.exp (3 * (1653191227 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1653191227 / 500000000) / 16) (929414491 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1653243417 / 500000000) : ℝ) / 16) ≤ (1858865363 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1653243417 / 500000000) / 16) (1858865363 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((409 / 16000) : ℝ) (1637 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1653191227 / 500000000) (1653243417 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (409 / 16000) (1637 / 64000) (526227220933 / 500000000000) (526243665791 / 500000000000) (1653191227 / 500000000) (1653243417 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (409 / 16000) (1637 / 64000) (1653191227 / 500000000) (1653243417 / 500000000) (3075481 / 62500000000) (49223109 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1653191227 / 500000000) (1653243417 / 500000000) (929414491 / 500000000) (1858865363 / 1000000000) (3075481 / 62500000000) (49223109 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0388 :
    ∀ t ∈ Set.Icc ((1637 / 64000) : ℝ) (819 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1052487331581 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1637 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1637 / 64000)) (1052487331581 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((819 / 32000) : ℝ)) ≤ (42100808893 / 40000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (819 / 32000)) (42100808893 / 40000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((371772999 / 200000000) : ℝ) ≤ Real.exp (3 * (165324289 / 50000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (165324289 / 50000000) / 16) (371772999 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3306590163 / 1000000000) : ℝ) / 16) ≤ (1858901377 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3306590163 / 1000000000) / 16) (1858901377 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1637 / 64000) : ℝ) (819 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (165324289 / 50000000) (3306590163 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1637 / 64000) (819 / 32000) (1052487331581 / 1000000000000) (42100808893 / 40000000000) (165324289 / 50000000) (3306590163 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1637 / 64000) (819 / 32000) (165324289 / 50000000) (3306590163 / 1000000000) (9838489 / 200000000000) (49207853 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (165324289 / 50000000) (3306590163 / 1000000000) (371772999 / 200000000) (1858901377 / 1000000000) (9838489 / 200000000000) (49207853 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0389 :
    ∀ t ∈ Set.Icc ((819 / 32000) : ℝ) (1639 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((263130055581 / 250000000000) : ℝ) ≤ Real.exp (2 * (819 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (819 / 32000)) (263130055581 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1639 / 64000) : ℝ)) ≤ (65784569631 / 62500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1639 / 64000)) (65784569631 / 62500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1858901009 / 1000000000) : ℝ) ≤ Real.exp (3 * (330658911 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (330658911 / 100000000) / 16) (1858901009 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((413336687 / 125000000) : ℝ) / 16) ≤ (929468697 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (413336687 / 125000000) / 16) (929468697 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((819 / 32000) : ℝ) (1639 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (330658911 / 100000000) (413336687 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (819 / 32000) (1639 / 64000) (263130055581 / 250000000000) (65784569631 / 62500000000) (330658911 / 100000000) (413336687 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (819 / 32000) (1639 / 64000) (330658911 / 100000000) (413336687 / 125000000) (24588599 / 500000000000) (24596301 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (330658911 / 100000000) (413336687 / 125000000) (1858901009 / 1000000000) (929468697 / 500000000) (24588599 / 500000000000) (24596301 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0390 :
    ∀ t ∈ Set.Icc ((1639 / 64000) : ℝ) (41 / 1600), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((210510622819 / 200000000000) : ℝ) ≤ Real.exp (2 * (1639 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1639 / 64000)) (210510622819 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((41 / 1600) : ℝ)) ≤ (210517201379 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (41 / 1600)) (210517201379 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((74357481 / 40000000) : ℝ) ≤ Real.exp (3 * (1653346221 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1653346221 / 500000000) / 16) (74357481 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((103337401 / 31250000) : ℝ) / 16) ≤ (464743353 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (103337401 / 31250000) / 16) (464743353 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1639 / 64000) : ℝ) (41 / 1600),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1653346221 / 500000000) (103337401 / 31250000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1639 / 64000) (41 / 1600) (210510622819 / 200000000000) (210517201379 / 200000000000) (1653346221 / 500000000) (103337401 / 31250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1639 / 64000) (41 / 1600) (1653346221 / 500000000) (103337401 / 31250000) (9832391 / 200000000000) (9835471 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1653346221 / 500000000) (103337401 / 31250000) (74357481 / 40000000) (464743353 / 250000000) (9832391 / 200000000000) (9835471 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0391 :
    ∀ t ∈ Set.Icc ((41 / 1600) : ℝ) (1641 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((526293003447 / 500000000000) : ℝ) ≤ Real.exp (2 * (41 / 1600)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (41 / 1600)) (526293003447 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1641 / 64000) : ℝ)) ≤ (526309450361 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1641 / 64000)) (526309450361 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((464743261 / 250000000) : ℝ) ≤ Real.exp (3 * (1653397889 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1653397889 / 500000000) / 16) (464743261 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3306900171 / 1000000000) : ℝ) / 16) ≤ (232376179 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3306900171 / 1000000000) / 16) (232376179 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((41 / 1600) : ℝ) (1641 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1653397889 / 500000000) (3306900171 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (41 / 1600) (1641 / 64000) (526293003447 / 500000000000) (526309450361 / 500000000000) (1653397889 / 500000000) (3306900171 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (41 / 1600) (1641 / 64000) (1653397889 / 500000000) (3306900171 / 1000000000) (12286679 / 250000000000) (49162111 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1653397889 / 500000000) (3306900171 / 1000000000) (464743261 / 250000000) (232376179 / 125000000) (12286679 / 250000000000) (49162111 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0392 :
    ∀ t ∈ Set.Icc ((1641 / 64000) : ℝ) (821 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1052618900721 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1641 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1641 / 64000)) (1052618900721 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((821 / 32000) : ℝ)) ≤ (131581474447 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (821 / 32000)) (131581474447 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1859009063 / 1000000000) : ℝ) ≤ Real.exp (3 * (3306899117 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3306899117 / 1000000000) / 16) (1859009063 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3307003513 / 1000000000) : ℝ) / 16) ≤ (929522727 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3307003513 / 1000000000) / 16) (929522727 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1641 / 64000) : ℝ) (821 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3306899117 / 1000000000) (3307003513 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1641 / 64000) (821 / 32000) (1052618900721 / 1000000000000) (131581474447 / 125000000000) (3306899117 / 1000000000) (3307003513 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1641 / 64000) (821 / 32000) (3306899117 / 1000000000) (3307003513 / 1000000000) (49131481 / 1000000000000) (49146873 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3306899117 / 1000000000) (3307003513 / 1000000000) (1859009063 / 1000000000) (929522727 / 500000000) (49131481 / 1000000000000) (49146873 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0393 :
    ∀ t ∈ Set.Icc ((821 / 32000) : ℝ) (1643 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((42106071823 / 40000000000) : ℝ) ≤ Real.exp (2 * (821 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (821 / 32000)) (42106071823 / 40000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1643 / 64000) : ℝ)) ≤ (1052684691459 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1643 / 64000)) (1052684691459 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((371809017 / 200000000) : ℝ) ≤ Real.exp (3 * (3307002459 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3307002459 / 1000000000) / 16) (371809017 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1653553429 / 500000000) : ℝ) / 16) ≤ (1859081477 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1653553429 / 500000000) / 16) (1859081477 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((821 / 32000) : ℝ) (1643 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3307002459 / 1000000000) (1653553429 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (821 / 32000) (1643 / 64000) (42106071823 / 40000000000) (1052684691459 / 1000000000000) (3307002459 / 1000000000) (1653553429 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (821 / 32000) (1643 / 64000) (3307002459 / 1000000000) (1653553429 / 500000000) (12279063 / 250000000000) (49131639 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3307002459 / 1000000000) (1653553429 / 500000000) (371809017 / 200000000) (1859081477 / 1000000000) (12279063 / 250000000000) (49131639 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0394 :
    ∀ t ∈ Set.Icc ((1643 / 64000) : ℝ) (411 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((526342345729 / 500000000000) : ℝ) ≤ Real.exp (2 * (1643 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1643 / 64000)) (526342345729 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((411 / 16000) : ℝ)) ≤ (1052717588369 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (411 / 16000)) (1052717588369 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1859081109 / 1000000000) : ℝ) ≤ Real.exp (3 * (661421161 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (661421161 / 200000000) / 16) (1859081109 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3307210207 / 1000000000) : ℝ) / 16) ≤ (929558751 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3307210207 / 1000000000) / 16) (929558751 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1643 / 64000) : ℝ) (411 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (661421161 / 200000000) (3307210207 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1643 / 64000) (411 / 16000) (526342345729 / 500000000000) (1052717588369 / 1000000000000) (661421161 / 200000000) (3307210207 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1643 / 64000) (411 / 16000) (661421161 / 200000000) (3307210207 / 1000000000) (24550513 / 500000000000) (6139551 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (661421161 / 200000000) (3307210207 / 1000000000) (1859081109 / 1000000000) (929558751 / 500000000) (24550513 / 500000000000) (6139551 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0395 :
    ∀ t ∈ Set.Icc ((411 / 16000) : ℝ) (329 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((65794849273 / 62500000000) : ℝ) ≤ Real.exp (2 * (411 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (411 / 16000)) (65794849273 / 62500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((329 / 12800) : ℝ)) ≤ (263187621577 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (329 / 12800)) (263187621577 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((929558567 / 500000000) : ℝ) ≤ Real.exp (3 * (3307209153 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3307209153 / 1000000000) / 16) (929558567 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3307313559 / 1000000000) : ℝ) / 16) ≤ (185915353 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3307313559 / 1000000000) / 16) (185915353 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((411 / 16000) : ℝ) (329 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3307209153 / 1000000000) (3307313559 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (411 / 16000) (329 / 12800) (65794849273 / 62500000000) (263187621577 / 250000000000) (3307209153 / 1000000000) (3307313559 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (411 / 16000) (329 / 12800) (3307209153 / 1000000000) (3307313559 / 1000000000) (12271451 / 250000000000) (24550591 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3307209153 / 1000000000) (3307313559 / 1000000000) (929558567 / 500000000) (185915353 / 100000000) (12271451 / 250000000000) (24550591 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0396 :
    ∀ t ∈ Set.Icc ((329 / 12800) : ℝ) (823 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1052750486307 / 1000000000000) : ℝ) ≤ Real.exp (2 * (329 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (329 / 12800)) (1052750486307 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((823 / 32000) : ℝ)) ≤ (42111335411 / 40000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (823 / 32000)) (42111335411 / 40000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1859153161 / 1000000000) : ℝ) ≤ Real.exp (3 * (661462501 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (661462501 / 200000000) / 16) (1859153161 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1653708457 / 500000000) : ℝ) / 16) ≤ (1859189559 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1653708457 / 500000000) / 16) (1859189559 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((329 / 12800) : ℝ) (823 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (661462501 / 200000000) (1653708457 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (329 / 12800) (823 / 32000) (1052750486307 / 1000000000000) (42111335411 / 40000000000) (661462501 / 200000000) (1653708457 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (329 / 12800) (823 / 32000) (661462501 / 200000000) (1653708457 / 500000000) (24535293 / 500000000000) (49085961 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (661462501 / 200000000) (1653708457 / 500000000) (1859153161 / 1000000000) (1859189559 / 1000000000) (24535293 / 500000000000) (49085961 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0397 :
    ∀ t ∈ Set.Icc ((823 / 32000) : ℝ) (1647 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((526391692637 / 500000000000) : ℝ) ≤ Real.exp (2 * (823 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (823 / 32000)) (526391692637 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1647 / 64000) : ℝ)) ≤ (105281628527 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1647 / 64000)) (105281628527 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((185918919 / 100000000) : ℝ) ≤ Real.exp (3 * (165370793 / 50000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (165370793 / 50000000) / 16) (185918919 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3307520273 / 1000000000) : ℝ) / 16) ≤ (185922559 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3307520273 / 1000000000) / 16) (185922559 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((823 / 32000) : ℝ) (1647 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (165370793 / 50000000) (3307520273 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (823 / 32000) (1647 / 64000) (526391692637 / 500000000000) (105281628527 / 100000000000) (165370793 / 50000000) (3307520273 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (823 / 32000) (1647 / 64000) (165370793 / 50000000) (3307520273 / 1000000000) (49055373 / 1000000000000) (49070743 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (165370793 / 50000000) (3307520273 / 1000000000) (185918919 / 100000000) (185922559 / 100000000) (49055373 / 1000000000000) (49070743 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0398 :
    ∀ t ∈ Set.Icc ((1647 / 64000) : ℝ) (103 / 4000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1052816285269 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1647 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1647 / 64000)) (1052816285269 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((103 / 4000) : ℝ)) ≤ (1052849186293 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (103 / 4000)) (1052849186293 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1859225221 / 1000000000) : ℝ) ≤ Real.exp (3 * (3307519219 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3307519219 / 1000000000) / 16) (1859225221 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1653811817 / 500000000) : ℝ) / 16) ≤ (929630811 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1653811817 / 500000000) / 16) (929630811 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1647 / 64000) : ℝ) (103 / 4000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3307519219 / 1000000000) (1653811817 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1647 / 64000) (103 / 4000) (1052816285269 / 1000000000000) (1052849186293 / 1000000000000) (3307519219 / 1000000000) (1653811817 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1647 / 64000) (103 / 4000) (3307519219 / 1000000000) (1653811817 / 500000000) (12260041 / 250000000000) (4905553 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3307519219 / 1000000000) (1653811817 / 500000000) (1859225221 / 1000000000) (929630811 / 500000000) (12260041 / 250000000000) (4905553 / 100000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0399 :
    ∀ t ∈ Set.Icc ((103 / 4000) : ℝ) (1649 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((263212296573 / 250000000000) : ℝ) ≤ Real.exp (2 * (103 / 4000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (103 / 4000)) (263212296573 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1649 / 64000) : ℝ)) ≤ (131610261043 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1649 / 64000)) (131610261043 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((929630627 / 500000000) : ℝ) ≤ Real.exp (3 * (165381129 / 50000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (165381129 / 50000000) / 16) (929630627 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3307726999 / 1000000000) : ℝ) / 16) ≤ (1859297657 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3307726999 / 1000000000) / 16) (1859297657 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((103 / 4000) : ℝ) (1649 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (165381129 / 50000000) (3307726999 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (103 / 4000) (1649 / 64000) (263212296573 / 250000000000) (131610261043 / 125000000000) (165381129 / 50000000) (3307726999 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (103 / 4000) (1649 / 64000) (165381129 / 50000000) (3307726999 / 1000000000) (49024959 / 1000000000000) (49040321 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (165381129 / 50000000) (3307726999 / 1000000000) (929630627 / 500000000) (1859297657 / 1000000000) (49024959 / 1000000000000) (49040321 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch019 :
    ∀ t ∈ Set.Icc ((1629 / 64000) : ℝ) (1649 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0380
      hpThetaDensityTwoTermCompact_cell0381)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0382
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0383
      hpThetaDensityTwoTermCompact_cell0384)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0385
      hpThetaDensityTwoTermCompact_cell0386)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0387
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0388
      hpThetaDensityTwoTermCompact_cell0389))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0390
      hpThetaDensityTwoTermCompact_cell0391)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0392
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0393
      hpThetaDensityTwoTermCompact_cell0394)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0395
      hpThetaDensityTwoTermCompact_cell0396)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0397
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0398
      hpThetaDensityTwoTermCompact_cell0399)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch019
end HodgeProofHP
