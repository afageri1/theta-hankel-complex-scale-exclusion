/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0080 :
    ∀ t ∈ Set.Icc ((1329 / 64000) : ℝ) (133 / 6400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1042405736521 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1329 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1329 / 64000)) (1042405736521 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((133 / 6400) : ℝ)) ≤ (1042438312211 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (133 / 6400)) (1042438312211 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((461964687 / 250000000) : ℝ) ≤ Real.exp (3 * (1637406761 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1637406761 / 500000000) / 16) (461964687 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((654983381 / 200000000) : ℝ) / 16) ≤ (1847894569 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (654983381 / 200000000) / 16) (1847894569 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1329 / 64000) : ℝ) (133 / 6400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1637406761 / 500000000) (654983381 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1329 / 64000) (133 / 6400) (1042405736521 / 1000000000000) (1042438312211 / 1000000000000) (1637406761 / 500000000) (654983381 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1329 / 64000) (133 / 6400) (1637406761 / 500000000) (654983381 / 200000000) (54095977 / 1000000000000) (54112759 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1637406761 / 500000000) (654983381 / 200000000) (461964687 / 250000000) (1847894569 / 1000000000) (54095977 / 1000000000000) (54112759 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0081 :
    ∀ t ∈ Set.Icc ((133 / 6400) : ℝ) (1331 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((104243831221 / 100000000000) : ℝ) ≤ Real.exp (2 * (133 / 6400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (133 / 6400)) (104243831221 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1331 / 64000) : ℝ)) ≤ (1042470888917 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1331 / 64000)) (1042470888917 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((923947103 / 500000000) : ℝ) ≤ Real.exp (3 * (1637457931 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1637457931 / 500000000) / 16) (923947103 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((204688703 / 62500000) : ℝ) / 16) ≤ (1847930029 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (204688703 / 62500000) / 16) (1847930029 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((133 / 6400) : ℝ) (1331 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1637457931 / 500000000) (204688703 / 62500000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (133 / 6400) (1331 / 64000) (104243831221 / 100000000000) (1042470888917 / 1000000000000) (1637457931 / 500000000) (204688703 / 62500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (133 / 6400) (1331 / 64000) (1637457931 / 500000000) (204688703 / 62500000) (54079371 / 1000000000000) (13524037 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1637457931 / 500000000) (204688703 / 62500000) (923947103 / 500000000) (1847930029 / 1000000000) (54079371 / 1000000000000) (13524037 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0082 :
    ∀ t ∈ Set.Icc ((1331 / 64000) : ℝ) (333 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((260617722229 / 250000000000) : ℝ) ≤ Real.exp (2 * (1331 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1331 / 64000)) (260617722229 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((333 / 16000) : ℝ)) ≤ (1042503466641 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (333 / 16000)) (1042503466641 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((923964833 / 500000000) : ℝ) ≤ Real.exp (3 * (818754551 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (818754551 / 250000000) / 16) (923964833 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1637560797 / 500000000) : ℝ) / 16) ≤ (1847965491 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1637560797 / 500000000) / 16) (1847965491 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1331 / 64000) : ℝ) (333 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (818754551 / 250000000) (1637560797 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1331 / 64000) (333 / 16000) (260617722229 / 250000000000) (1042503466641 / 1000000000000) (818754551 / 250000000) (1637560797 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1331 / 64000) (333 / 16000) (818754551 / 250000000) (1637560797 / 500000000) (54062769 / 1000000000000) (27039771 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (818754551 / 250000000) (1637560797 / 500000000) (923964833 / 500000000) (1847965491 / 1000000000) (54062769 / 1000000000000) (27039771 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0083 :
    ∀ t ∈ Set.Icc ((333 / 16000) : ℝ) (1333 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((13031293333 / 12500000000) : ℝ) ≤ Real.exp (2 * (333 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (333 / 16000)) (13031293333 / 12500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1333 / 64000) : ℝ)) ≤ (1042536045383 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1333 / 64000)) (1042536045383 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((230995641 / 125000000) : ℝ) ≤ Real.exp (3 * (65502411 / 20000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (65502411 / 20000000) / 16) (230995641 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3275223943 / 1000000000) : ℝ) / 16) ≤ (924000477 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3275223943 / 1000000000) / 16) (924000477 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((333 / 16000) : ℝ) (1333 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (65502411 / 20000000) (3275223943 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (333 / 16000) (1333 / 64000) (13031293333 / 12500000000) (1042536045383 / 1000000000000) (65502411 / 20000000) (3275223943 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (333 / 16000) (1333 / 64000) (65502411 / 20000000) (3275223943 / 1000000000) (13511543 / 250000000000) (2703147 / 50000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (65502411 / 20000000) (3275223943 / 1000000000) (230995641 / 125000000) (924000477 / 500000000) (13511543 / 250000000000) (2703147 / 50000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0084 :
    ∀ t ∈ Set.Icc ((1333 / 64000) : ℝ) (667 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((521268022691 / 500000000000) : ℝ) ≤ Real.exp (2 * (1333 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1333 / 64000)) (521268022691 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((667 / 32000) : ℝ)) ≤ (130321078143 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (667 / 32000)) (130321078143 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1848000591 / 1000000000) : ℝ) ≤ Real.exp (3 * (3275222899 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3275222899 / 1000000000) / 16) (1848000591 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((655065259 / 200000000) : ℝ) / 16) ≤ (92401821 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (655065259 / 200000000) / 16) (92401821 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1333 / 64000) : ℝ) (667 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3275222899 / 1000000000) (655065259 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1333 / 64000) (667 / 32000) (521268022691 / 500000000000) (130321078143 / 125000000000) (3275222899 / 1000000000) (655065259 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1333 / 64000) (667 / 32000) (3275222899 / 1000000000) (655065259 / 200000000) (54029579 / 1000000000000) (54046343 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3275222899 / 1000000000) (655065259 / 200000000) (1848000591 / 1000000000) (92401821 / 50000000) (54029579 / 1000000000000) (54046343 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0085 :
    ∀ t ∈ Set.Icc ((667 / 32000) : ℝ) (267 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1042568625143 / 1000000000000) : ℝ) ≤ Real.exp (2 * (667 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (667 / 32000)) (1042568625143 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((267 / 12800) : ℝ)) ≤ (1042601205923 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (267 / 12800)) (1042601205923 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1848036057 / 1000000000) : ℝ) ≤ Real.exp (3 * (818831313 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (818831313 / 250000000) / 16) (1848036057 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3275428651 / 1000000000) : ℝ) / 16) ≤ (1848071887 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3275428651 / 1000000000) / 16) (1848071887 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((667 / 32000) : ℝ) (267 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (818831313 / 250000000) (3275428651 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (667 / 32000) (267 / 12800) (1042568625143 / 1000000000000) (1042601205923 / 1000000000000) (818831313 / 250000000) (3275428651 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (667 / 32000) (267 / 12800) (818831313 / 250000000) (3275428651 / 1000000000) (54012991 / 1000000000000) (216119 / 4000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (818831313 / 250000000) (3275428651 / 1000000000) (1848036057 / 1000000000) (1848071887 / 1000000000) (54012991 / 1000000000000) (216119 / 4000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0086 :
    ∀ t ∈ Set.Icc ((267 / 12800) : ℝ) (167 / 8000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((521300602961 / 500000000000) : ℝ) ≤ Real.exp (2 * (267 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (267 / 12800)) (521300602961 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((167 / 8000) : ℝ)) ≤ (1042633787719 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (167 / 8000)) (1042633787719 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((462017881 / 250000000) : ℝ) ≤ Real.exp (3 * (3275427607 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3275427607 / 1000000000) / 16) (462017881 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((327553101 / 100000000) : ℝ) / 16) ≤ (462026839 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (327553101 / 100000000) / 16) (462026839 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((267 / 12800) : ℝ) (167 / 8000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3275427607 / 1000000000) (327553101 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (267 / 12800) (167 / 8000) (521300602961 / 500000000000) (1042633787719 / 1000000000000) (3275427607 / 1000000000) (327553101 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (267 / 12800) (167 / 8000) (3275427607 / 1000000000) (327553101 / 100000000) (53996407 / 1000000000000) (27006581 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3275427607 / 1000000000) (327553101 / 100000000) (462017881 / 250000000) (462026839 / 250000000) (53996407 / 1000000000000) (27006581 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0087 :
    ∀ t ∈ Set.Icc ((167 / 8000) : ℝ) (1337 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((521316893859 / 500000000000) : ℝ) ≤ Real.exp (2 * (167 / 8000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (167 / 8000)) (521316893859 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1337 / 64000) : ℝ)) ≤ (521333185267 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1337 / 64000)) (521333185267 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1848106993 / 1000000000) : ℝ) ≤ Real.exp (3 * (1637764983 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1637764983 / 500000000) / 16) (1848106993 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((818908343 / 250000000) : ℝ) / 16) ≤ (1848142827 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (818908343 / 250000000) / 16) (1848142827 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((167 / 8000) : ℝ) (1337 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1637764983 / 500000000) (818908343 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (167 / 8000) (1337 / 64000) (521316893859 / 500000000000) (521333185267 / 500000000000) (1637764983 / 500000000) (818908343 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (167 / 8000) (1337 / 64000) (1637764983 / 500000000) (818908343 / 250000000) (13494957 / 250000000000) (26998289 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1637764983 / 500000000) (818908343 / 250000000) (1848106993 / 1000000000) (1848142827 / 1000000000) (13494957 / 250000000000) (26998289 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0088 :
    ∀ t ∈ Set.Icc ((1337 / 64000) : ℝ) (669 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1042666370533 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1337 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1337 / 64000)) (1042666370533 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((669 / 32000) : ℝ)) ≤ (1042698954367 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (669 / 32000)) (1042698954367 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((14438613 / 7812500) : ℝ) ≤ Real.exp (3 * (409454041 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (409454041 / 125000000) / 16) (14438613 / 7812500) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3275735737 / 1000000000) : ℝ) / 16) ≤ (1848178299 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3275735737 / 1000000000) / 16) (1848178299 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1337 / 64000) : ℝ) (669 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (409454041 / 125000000) (3275735737 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1337 / 64000) (669 / 32000) (1042666370533 / 1000000000000) (1042698954367 / 1000000000000) (409454041 / 125000000) (3275735737 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1337 / 64000) (669 / 32000) (409454041 / 125000000) (3275735737 / 1000000000) (26981627 / 500000000000) (53979999 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (409454041 / 125000000) (3275735737 / 1000000000) (14438613 / 7812500) (1848178299 / 1000000000) (26981627 / 500000000000) (53979999 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0089 :
    ∀ t ∈ Set.Icc ((669 / 32000) : ℝ) (1339 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((521349477183 / 500000000000) : ℝ) ≤ Real.exp (2 * (669 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (669 / 32000)) (521349477183 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1339 / 64000) : ℝ)) ≤ (1042731539219 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1339 / 64000)) (1042731539219 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1848177937 / 1000000000) : ℝ) ≤ Real.exp (3 * (3275734693 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3275734693 / 1000000000) / 16) (1848177937 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((655167621 / 200000000) : ℝ) / 16) ≤ (924106887 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (655167621 / 200000000) / 16) (924106887 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((669 / 32000) : ℝ) (1339 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3275734693 / 1000000000) (655167621 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (669 / 32000) (1339 / 64000) (521349477183 / 500000000000) (1042731539219 / 1000000000000) (3275734693 / 1000000000) (655167621 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (669 / 32000) (1339 / 64000) (3275734693 / 1000000000) (655167621 / 200000000) (13486671 / 250000000000) (1686357 / 31250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3275734693 / 1000000000) (655167621 / 200000000) (1848177937 / 1000000000) (924106887 / 500000000) (13486671 / 250000000000) (1686357 / 31250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0090 :
    ∀ t ∈ Set.Icc ((1339 / 64000) : ℝ) (67 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((521365769609 / 500000000000) : ℝ) ≤ Real.exp (2 * (1339 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1339 / 64000)) (521365769609 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((67 / 3200) : ℝ)) ≤ (1042764125089 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (67 / 3200)) (1042764125089 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1848213411 / 1000000000) : ℝ) ≤ Real.exp (3 * (3275837061 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3275837061 / 1000000000) / 16) (1848213411 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3275940477 / 1000000000) : ℝ) / 16) ≤ (7392997 / 4000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3275940477 / 1000000000) / 16) (7392997 / 4000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1339 / 64000) : ℝ) (67 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3275837061 / 1000000000) (3275940477 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1339 / 64000) (67 / 3200) (521365769609 / 500000000000) (1042764125089 / 1000000000000) (3275837061 / 1000000000) (3275940477 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1339 / 64000) (67 / 3200) (3275837061 / 1000000000) (3275940477 / 1000000000) (53930119 / 1000000000000) (10789371 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3275837061 / 1000000000) (3275940477 / 1000000000) (1848213411 / 1000000000) (7392997 / 4000000) (53930119 / 1000000000000) (10789371 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0091 :
    ∀ t ∈ Set.Icc ((67 / 3200) : ℝ) (1341 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((32586378909 / 31250000000) : ℝ) ≤ Real.exp (2 * (67 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (67 / 3200)) (32586378909 / 31250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1341 / 64000) : ℝ)) ≤ (1042796711977 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1341 / 64000)) (1042796711977 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1848248887 / 1000000000) : ℝ) ≤ Real.exp (3 * (3275939433 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3275939433 / 1000000000) / 16) (1848248887 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3276042851 / 1000000000) : ℝ) / 16) ≤ (231035591 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3276042851 / 1000000000) / 16) (231035591 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((67 / 3200) : ℝ) (1341 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3275939433 / 1000000000) (3276042851 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (67 / 3200) (1341 / 64000) (32586378909 / 31250000000) (1042796711977 / 1000000000000) (3275939433 / 1000000000) (3276042851 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (67 / 3200) (1341 / 64000) (3275939433 / 1000000000) (3276042851 / 1000000000) (26956779 / 500000000000) (53930289 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3275939433 / 1000000000) (3276042851 / 1000000000) (1848248887 / 1000000000) (231035591 / 125000000) (26956779 / 500000000000) (53930289 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0092 :
    ∀ t ∈ Set.Icc ((1341 / 64000) : ℝ) (671 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((130349588997 / 125000000000) : ℝ) ≤ Real.exp (2 * (1341 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1341 / 64000)) (130349588997 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((671 / 32000) : ℝ)) ≤ (1042829299883 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (671 / 32000)) (1042829299883 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((369656873 / 200000000) : ℝ) ≤ Real.exp (3 * (3276041807 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3276041807 / 1000000000) / 16) (369656873 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3276145229 / 1000000000) : ℝ) / 16) ≤ (115520013 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3276145229 / 1000000000) / 16) (115520013 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1341 / 64000) : ℝ) (671 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3276041807 / 1000000000) (3276145229 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1341 / 64000) (671 / 32000) (130349588997 / 125000000000) (1042829299883 / 1000000000000) (3276041807 / 1000000000) (3276145229 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1341 / 64000) (671 / 32000) (3276041807 / 1000000000) (3276145229 / 1000000000) (26948501 / 500000000000) (53913729 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3276041807 / 1000000000) (3276145229 / 1000000000) (369656873 / 200000000) (115520013 / 62500000) (26948501 / 500000000000) (53913729 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0093 :
    ∀ t ∈ Set.Icc ((671 / 32000) : ℝ) (1343 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((521414649941 / 500000000000) : ℝ) ≤ Real.exp (2 * (671 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (671 / 32000)) (521414649941 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1343 / 64000) : ℝ)) ≤ (130357736101 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1343 / 64000)) (130357736101 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((369663969 / 200000000) : ℝ) ≤ Real.exp (3 * (655228837 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (655228837 / 200000000) / 16) (369663969 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((327624761 / 100000000) : ℝ) / 16) ≤ (1848355689 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (327624761 / 100000000) / 16) (1848355689 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((671 / 32000) : ℝ) (1343 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (655228837 / 200000000) (327624761 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (671 / 32000) (1343 / 64000) (521414649941 / 500000000000) (130357736101 / 125000000000) (655228837 / 200000000) (327624761 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (671 / 32000) (1343 / 64000) (655228837 / 200000000) (327624761 / 100000000) (53880451 / 1000000000000) (13474293 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (655228837 / 200000000) (327624761 / 100000000) (369663969 / 200000000) (1848355689 / 1000000000) (53880451 / 1000000000000) (13474293 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0094 :
    ∀ t ∈ Set.Icc ((1343 / 64000) : ℝ) (21 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1042861888807 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1343 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1343 / 64000)) (1042861888807 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((21 / 1000) : ℝ)) ≤ (1042894478751 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (21 / 1000)) (1042894478751 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((924177663 / 500000000) : ℝ) ≤ Real.exp (3 * (1638123283 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1638123283 / 500000000) / 16) (924177663 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((655269999 / 200000000) : ℝ) / 16) ≤ (1848391173 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (655269999 / 200000000) / 16) (1848391173 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1343 / 64000) : ℝ) (21 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1638123283 / 500000000) (655269999 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1343 / 64000) (21 / 1000) (1042861888807 / 1000000000000) (1042894478751 / 1000000000000) (1638123283 / 500000000) (655269999 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1343 / 64000) (21 / 1000) (1638123283 / 500000000) (655269999 / 200000000) (53863903 / 1000000000000) (53880621 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1638123283 / 500000000) (655269999 / 200000000) (924177663 / 500000000) (1848391173 / 1000000000) (53863903 / 1000000000000) (53880621 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0095 :
    ∀ t ∈ Set.Icc ((21 / 1000) : ℝ) (269 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((834315583 / 800000000) : ℝ) ≤ Real.exp (2 * (21 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (21 / 1000)) (834315583 / 800000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((269 / 12800) : ℝ)) ≤ (1042927069713 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (269 / 12800)) (1042927069713 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((184839081 / 100000000) : ℝ) ≤ Real.exp (3 * (3276348951 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3276348951 / 1000000000) / 16) (184839081 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1638226191 / 500000000) : ℝ) / 16) ≤ (924213329 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1638226191 / 500000000) / 16) (924213329 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((21 / 1000) : ℝ) (269 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3276348951 / 1000000000) (1638226191 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (21 / 1000) (269 / 12800) (834315583 / 800000000) (1042927069713 / 1000000000000) (3276348951 / 1000000000) (1638226191 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (21 / 1000) (269 / 12800) (3276348951 / 1000000000) (1638226191 / 500000000) (53847361 / 1000000000000) (26932037 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3276348951 / 1000000000) (1638226191 / 500000000) (184839081 / 100000000) (924213329 / 500000000) (53847361 / 1000000000000) (26932037 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0096 :
    ∀ t ∈ Set.Icc ((269 / 12800) : ℝ) (673 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((65182941857 / 62500000000) : ℝ) ≤ Real.exp (2 * (269 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (269 / 12800)) (65182941857 / 62500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((673 / 32000) : ℝ)) ≤ (1042959661693 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (673 / 32000)) (1042959661693 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((369685259 / 200000000) : ℝ) ≤ Real.exp (3 * (1638225669 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1638225669 / 500000000) / 16) (369685259 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3276554773 / 1000000000) : ℝ) / 16) ≤ (369692429 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3276554773 / 1000000000) / 16) (369692429 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((269 / 12800) : ℝ) (673 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1638225669 / 500000000) (3276554773 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (269 / 12800) (673 / 32000) (65182941857 / 62500000000) (1042959661693 / 1000000000000) (1638225669 / 500000000) (3276554773 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (269 / 12800) (673 / 32000) (1638225669 / 500000000) (3276554773 / 1000000000) (53830823 / 1000000000000) (53847531 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1638225669 / 500000000) (3276554773 / 1000000000) (369685259 / 200000000) (369692429 / 200000000) (53830823 / 1000000000000) (53847531 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0097 :
    ∀ t ∈ Set.Icc ((673 / 32000) : ℝ) (1347 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((260739915423 / 250000000000) : ℝ) ≤ Real.exp (2 * (673 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (673 / 32000)) (260739915423 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1347 / 64000) : ℝ)) ≤ (260748063673 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1347 / 64000)) (260748063673 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((924230891 / 500000000) : ℝ) ≤ Real.exp (3 * (3276553729 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3276553729 / 1000000000) / 16) (924230891 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3276657167 / 1000000000) : ℝ) / 16) ≤ (1848497633 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3276657167 / 1000000000) / 16) (1848497633 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((673 / 32000) : ℝ) (1347 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3276553729 / 1000000000) (3276657167 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (673 / 32000) (1347 / 64000) (260739915423 / 250000000000) (260748063673 / 250000000000) (3276553729 / 1000000000) (3276657167 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (673 / 32000) (1347 / 64000) (3276553729 / 1000000000) (3276657167 / 1000000000) (5381429 / 100000000000) (53830993 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3276553729 / 1000000000) (3276657167 / 1000000000) (924230891 / 500000000) (1848497633 / 1000000000) (5381429 / 100000000000) (53830993 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0098 :
    ∀ t ∈ Set.Icc ((1347 / 64000) : ℝ) (337 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1042992254691 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1347 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1347 / 64000)) (1042992254691 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((337 / 16000) : ℝ)) ≤ (1043024848709 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (337 / 16000)) (1043024848709 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((184849727 / 100000000) : ℝ) ≤ Real.exp (3 * (3276656123 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3276656123 / 1000000000) / 16) (184849727 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((819189891 / 250000000) : ℝ) / 16) ≤ (462133281 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (819189891 / 250000000) / 16) (462133281 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1347 / 64000) : ℝ) (337 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3276656123 / 1000000000) (819189891 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1347 / 64000) (337 / 16000) (1042992254691 / 1000000000000) (1043024848709 / 1000000000000) (3276656123 / 1000000000) (819189891 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1347 / 64000) (337 / 16000) (3276656123 / 1000000000) (819189891 / 250000000) (53797761 / 1000000000000) (2690723 / 50000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3276656123 / 1000000000) (819189891 / 250000000) (184849727 / 100000000) (462133281 / 250000000) (53797761 / 1000000000000) (2690723 / 50000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0099 :
    ∀ t ∈ Set.Icc ((337 / 16000) : ℝ) (1349 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((260756212177 / 250000000000) : ℝ) ≤ Real.exp (2 * (337 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (337 / 16000)) (260756212177 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1349 / 64000) : ℝ)) ≤ (208611488749 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1349 / 64000)) (208611488749 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1848532761 / 1000000000) : ℝ) ≤ Real.exp (3 * (81918963 / 25000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (81918963 / 25000000) / 16) (1848532761 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((819215491 / 250000000) : ℝ) / 16) ≤ (231071077 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (819215491 / 250000000) / 16) (231071077 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((337 / 16000) : ℝ) (1349 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (81918963 / 25000000) (819215491 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (337 / 16000) (1349 / 64000) (260756212177 / 250000000000) (208611488749 / 200000000000) (81918963 / 25000000) (819215491 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (337 / 16000) (1349 / 64000) (81918963 / 25000000) (819215491 / 250000000) (53781237 / 1000000000000) (53797931 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (81918963 / 25000000) (819215491 / 250000000) (1848532761 / 1000000000) (231071077 / 125000000) (53781237 / 1000000000000) (53797931 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch004 :
    ∀ t ∈ Set.Icc ((1329 / 64000) : ℝ) (1349 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0080
      hpThetaDensityTwoTermCompact_cell0081)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0082
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0083
      hpThetaDensityTwoTermCompact_cell0084)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0085
      hpThetaDensityTwoTermCompact_cell0086)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0087
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0088
      hpThetaDensityTwoTermCompact_cell0089))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0090
      hpThetaDensityTwoTermCompact_cell0091)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0092
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0093
      hpThetaDensityTwoTermCompact_cell0094)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0095
      hpThetaDensityTwoTermCompact_cell0096)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0097
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0098
      hpThetaDensityTwoTermCompact_cell0099)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch004
end HodgeProofHP
