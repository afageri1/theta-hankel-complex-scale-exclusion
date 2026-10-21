/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0720 :
    ∀ t ∈ Set.Icc ((2463 / 64000) : ℝ) (2467 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((216001665121 / 200000000000) : ℝ) ≤ Real.exp (2 * (2463 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2463 / 64000)) (216001665121 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2467 / 64000) : ℝ)) ≤ (270035833771 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2467 / 64000)) (270035833771 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((188924501 / 100000000) : ℝ) ≤ Real.exp (3 * (678589103 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (678589103 / 200000000) / 16) (188924501 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3393370741 / 1000000000) : ℝ) / 16) ≤ (1889395647 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3393370741 / 1000000000) / 16) (1889395647 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2463 / 64000) : ℝ) (2467 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (678589103 / 200000000) (3393370741 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2463 / 64000) (2467 / 64000) (216001665121 / 200000000000) (270035833771 / 250000000000) (678589103 / 200000000) (3393370741 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2463 / 64000) (2467 / 64000) (678589103 / 200000000) (3393370741 / 1000000000) (37916953 / 1000000000000) (7593071 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (678589103 / 200000000) (3393370741 / 1000000000) (188924501 / 100000000) (1889395647 / 1000000000) (37916953 / 1000000000000) (7593071 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0721 :
    ∀ t ∈ Set.Icc ((2467 / 64000) : ℝ) (2471 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1080143335083 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2467 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2467 / 64000)) (1080143335083 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2471 / 64000) : ℝ)) ≤ (6751739759 / 6250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2471 / 64000)) (6751739759 / 6250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1889395263 / 1000000000) : ℝ) ≤ Real.exp (3 * (169668483 / 50000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (169668483 / 50000000) / 16) (1889395263 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3393794939 / 1000000000) : ℝ) / 16) ≤ (188954593 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3393794939 / 1000000000) / 16) (188954593 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2467 / 64000) : ℝ) (2471 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (169668483 / 50000000) (3393794939 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2467 / 64000) (2471 / 64000) (1080143335083 / 1000000000000) (6751739759 / 6250000000) (169668483 / 50000000) (3393794939 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2467 / 64000) (2471 / 64000) (169668483 / 50000000) (3393794939 / 1000000000) (37868731 / 1000000000000) (37917077 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (169668483 / 50000000) (3393794939 / 1000000000) (1889395263 / 1000000000) (188954593 / 100000000) (37868731 / 1000000000000) (37917077 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0722 :
    ∀ t ∈ Set.Icc ((2471 / 64000) : ℝ) (99 / 2560), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1080278361439 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2471 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2471 / 64000)) (1080278361439 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((99 / 2560) : ℝ)) ≤ (43216536187 / 40000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (99 / 2560)) (43216536187 / 40000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((944772773 / 500000000) : ℝ) ≤ Real.exp (3 * (1696896929 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1696896929 / 500000000) / 16) (944772773 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((339421919 / 100000000) : ℝ) / 16) ≤ (1889696243 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (339421919 / 100000000) / 16) (1889696243 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2471 / 64000) : ℝ) (99 / 2560),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1696896929 / 500000000) (339421919 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2471 / 64000) (99 / 2560) (1080278361439 / 1000000000000) (43216536187 / 40000000000) (1696896929 / 500000000) (339421919 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2471 / 64000) (99 / 2560) (1696896929 / 500000000) (339421919 / 100000000) (9455141 / 250000000000) (7573771 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1696896929 / 500000000) (339421919 / 100000000) (944772773 / 500000000) (1889696243 / 1000000000) (9455141 / 250000000000) (7573771 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0723 :
    ∀ t ∈ Set.Icc ((99 / 2560) : ℝ) (2479 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((540206702337 / 500000000000) : ℝ) ≤ Real.exp (2 * (99 / 2560)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (99 / 2560)) (540206702337 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2479 / 64000) : ℝ)) ≤ (135068558099 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2479 / 64000)) (135068558099 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1889695859 / 1000000000) : ℝ) ≤ Real.exp (3 * (848554527 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (848554527 / 250000000) / 16) (1889695859 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1697321747 / 500000000) : ℝ) / 16) ≤ (472461647 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1697321747 / 500000000) / 16) (472461647 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((99 / 2560) : ℝ) (2479 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (848554527 / 250000000) (1697321747 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (99 / 2560) (2479 / 64000) (540206702337 / 500000000000) (135068558099 / 125000000000) (848554527 / 250000000) (1697321747 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (99 / 2560) (2479 / 64000) (848554527 / 250000000) (1697321747 / 500000000) (9443113 / 250000000000) (2363793 / 62500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (848554527 / 250000000) (1697321747 / 500000000) (1889695859 / 1000000000) (472461647 / 250000000) (9443113 / 250000000000) (2363793 / 62500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0724 :
    ∀ t ∈ Set.Icc ((2479 / 64000) : ℝ) (2483 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1080548464791 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2479 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2479 / 64000)) (1080548464791 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2483 / 64000) : ℝ)) ≤ (33771360681 / 31250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2483 / 64000)) (33771360681 / 31250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((472461551 / 250000000) : ℝ) ≤ Real.exp (3 * (848660603 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (848660603 / 250000000) / 16) (472461551 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3395067851 / 1000000000) : ℝ) / 16) ≤ (1889996963 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3395067851 / 1000000000) / 16) (1889996963 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2479 / 64000) : ℝ) (2483 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (848660603 / 250000000) (3395067851 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2479 / 64000) (2483 / 64000) (1080548464791 / 1000000000000) (33771360681 / 31250000000) (848660603 / 250000000) (3395067851 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2479 / 64000) (2483 / 64000) (848660603 / 250000000) (3395067851 / 1000000000) (9431099 / 250000000000) (1180393 / 31250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (848660603 / 250000000) (3395067851 / 1000000000) (472461551 / 250000000) (1889996963 / 1000000000) (9431099 / 250000000000) (1180393 / 31250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0725 :
    ∀ t ∈ Set.Icc ((2483 / 64000) : ℝ) (2487 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1080683541791 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2483 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2483 / 64000)) (1080683541791 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2487 / 64000) : ℝ)) ≤ (540409317839 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2487 / 64000)) (540409317839 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1889996579 / 1000000000) : ℝ) ≤ Real.exp (3 * (3395066769 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3395066769 / 1000000000) / 16) (1889996579 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3395492261 / 1000000000) : ℝ) / 16) ≤ (1890147369 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3395492261 / 1000000000) / 16) (1890147369 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2483 / 64000) : ℝ) (2487 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3395066769 / 1000000000) (3395492261 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2483 / 64000) (2487 / 64000) (1080683541791 / 1000000000000) (540409317839 / 500000000000) (3395066769 / 1000000000) (3395492261 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2483 / 64000) (2487 / 64000) (3395066769 / 1000000000) (3395492261 / 1000000000) (7535279 / 200000000000) (37724519 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3395066769 / 1000000000) (3395492261 / 1000000000) (1889996579 / 1000000000) (1890147369 / 1000000000) (7535279 / 200000000000) (37724519 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0726 :
    ∀ t ∈ Set.Icc ((2487 / 64000) : ℝ) (2491 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1080818635677 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2487 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2487 / 64000)) (1080818635677 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2491 / 64000) : ℝ)) ≤ (270238436613 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2491 / 64000)) (270238436613 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((378029397 / 200000000) : ℝ) ≤ Real.exp (3 * (3395491179 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3395491179 / 1000000000) / 16) (378029397 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((848979181 / 250000000) : ℝ) / 16) ≤ (945148903 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (848979181 / 250000000) / 16) (945148903 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2487 / 64000) : ℝ) (2491 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3395491179 / 1000000000) (848979181 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2487 / 64000) (2491 / 64000) (1080818635677 / 1000000000000) (270238436613 / 250000000000) (3395491179 / 1000000000) (848979181 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2487 / 64000) (2491 / 64000) (3395491179 / 1000000000) (848979181 / 250000000) (1175889 / 31250000000) (18838259 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3395491179 / 1000000000) (848979181 / 250000000) (378029397 / 200000000) (945148903 / 500000000) (1175889 / 31250000000) (18838259 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0727 :
    ∀ t ∈ Set.Icc ((2491 / 64000) : ℝ) (499 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1080953746451 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2491 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2491 / 64000)) (1080953746451 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((499 / 12800) : ℝ)) ≤ (216217774823 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (499 / 12800)) (216217774823 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((945148711 / 500000000) : ℝ) ≤ Real.exp (3 * (1697957821 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1697957821 / 500000000) / 16) (945148711 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((84908531 / 25000000) : ℝ) / 16) ≤ (945224137 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (84908531 / 25000000) / 16) (945224137 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2491 / 64000) : ℝ) (499 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1697957821 / 500000000) (84908531 / 25000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2491 / 64000) (499 / 12800) (1080953746451 / 1000000000000) (216217774823 / 200000000000) (1697957821 / 500000000) (84908531 / 25000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2491 / 64000) (499 / 12800) (1697957821 / 500000000) (84908531 / 25000000) (37580557 / 1000000000000) (9407143 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1697957821 / 500000000) (84908531 / 25000000) (945148711 / 500000000) (945224137 / 500000000) (37580557 / 1000000000000) (9407143 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0728 :
    ∀ t ∈ Set.Icc ((499 / 12800) : ℝ) (2499 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((540544437057 / 500000000000) : ℝ) ≤ Real.exp (2 * (499 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (499 / 12800)) (540544437057 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2499 / 64000) : ℝ)) ≤ (1081224018671 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2499 / 64000)) (1081224018671 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1890447889 / 1000000000) : ℝ) ≤ Real.exp (3 * (1698170079 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1698170079 / 500000000) / 16) (1890447889 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3396765809 / 1000000000) : ℝ) / 16) ≤ (472649693 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3396765809 / 1000000000) / 16) (472649693 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((499 / 12800) : ℝ) (2499 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1698170079 / 500000000) (3396765809 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (499 / 12800) (2499 / 64000) (540544437057 / 500000000000) (1081224018671 / 1000000000000) (1698170079 / 500000000) (3396765809 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (499 / 12800) (2499 / 64000) (1698170079 / 500000000) (3396765809 / 1000000000) (37532721 / 1000000000000) (37580681 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1698170079 / 500000000) (3396765809 / 1000000000) (1890447889 / 1000000000) (472649693 / 250000000) (37532721 / 1000000000000) (37580681 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0729 :
    ∀ t ∈ Set.Icc ((2499 / 64000) : ℝ) (2503 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((108122401867 / 100000000000) : ℝ) ≤ Real.exp (2 * (2499 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2499 / 64000)) (108122401867 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2503 / 64000) : ℝ)) ≤ (1081359180121 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2503 / 64000)) (1081359180121 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1890598387 / 1000000000) : ℝ) ≤ Real.exp (3 * (3396764727 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3396764727 / 1000000000) / 16) (1890598387 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3397190431 / 1000000000) : ℝ) / 16) ≤ (1890749301 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3397190431 / 1000000000) / 16) (1890749301 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2499 / 64000) : ℝ) (2503 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3396764727 / 1000000000) (3397190431 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2499 / 64000) (2503 / 64000) (108122401867 / 100000000000) (1081359180121 / 1000000000000) (3396764727 / 1000000000) (3397190431 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2499 / 64000) (2503 / 64000) (3396764727 / 1000000000) (3397190431 / 1000000000) (1874247 / 50000000000) (9383211 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3396764727 / 1000000000) (3397190431 / 1000000000) (1890598387 / 1000000000) (1890749301 / 1000000000) (1874247 / 50000000000) (9383211 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0730 :
    ∀ t ∈ Set.Icc ((2503 / 64000) : ℝ) (2507 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((27033979503 / 25000000000) : ℝ) ≤ Real.exp (2 * (2503 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2503 / 64000)) (27033979503 / 25000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2507 / 64000) : ℝ)) ≤ (1081494358467 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2507 / 64000)) (1081494358467 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((472687229 / 250000000) : ℝ) ≤ Real.exp (3 * (3397189349 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3397189349 / 1000000000) / 16) (472687229 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3397615107 / 1000000000) : ℝ) / 16) ≤ (1890899861 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3397615107 / 1000000000) / 16) (1890899861 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2503 / 64000) : ℝ) (2507 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3397189349 / 1000000000) (3397615107 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2503 / 64000) (2507 / 64000) (27033979503 / 25000000000) (1081494358467 / 1000000000000) (3397189349 / 1000000000) (3397615107 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2503 / 64000) (2507 / 64000) (3397189349 / 1000000000) (3397615107 / 1000000000) (37437213 / 1000000000000) (37485063 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3397189349 / 1000000000) (3397615107 / 1000000000) (472687229 / 250000000) (1890899861 / 1000000000) (37437213 / 1000000000000) (37485063 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0731 :
    ∀ t ∈ Set.Icc ((2507 / 64000) : ℝ) (2511 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((540747179233 / 500000000000) : ℝ) ≤ Real.exp (2 * (2507 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2507 / 64000)) (540747179233 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2511 / 64000) : ℝ)) ≤ (1081629553711 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2511 / 64000)) (1081629553711 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((472724869 / 250000000) : ℝ) ≤ Real.exp (3 * (424701753 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (424701753 / 125000000) / 16) (472724869 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((679607967 / 200000000) : ℝ) / 16) ≤ (472762613 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (679607967 / 200000000) / 16) (472762613 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2507 / 64000) : ℝ) (2511 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (424701753 / 125000000) (679607967 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2507 / 64000) (2511 / 64000) (540747179233 / 500000000000) (1081629553711 / 1000000000000) (424701753 / 125000000) (679607967 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2507 / 64000) (2511 / 64000) (424701753 / 125000000) (679607967 / 200000000) (18694771 / 500000000000) (4679667 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (424701753 / 125000000) (679607967 / 200000000) (472724869 / 250000000) (472762613 / 250000000) (18694771 / 500000000000) (4679667 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0732 :
    ∀ t ∈ Set.Icc ((2511 / 64000) : ℝ) (503 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((108162955371 / 100000000000) : ℝ) ≤ Real.exp (2 * (2511 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2511 / 64000)) (108162955371 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((503 / 12800) : ℝ)) ≤ (33805148933 / 31250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (503 / 12800)) (33805148933 / 31250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1891050067 / 1000000000) : ℝ) ≤ Real.exp (3 * (106188711 / 31250000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (106188711 / 31250000) / 16) (1891050067 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3398464617 / 1000000000) : ℝ) / 16) ≤ (945600537 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3398464617 / 1000000000) / 16) (945600537 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2511 / 64000) : ℝ) (503 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (106188711 / 31250000) (3398464617 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2511 / 64000) (503 / 12800) (108162955371 / 100000000000) (33805148933 / 31250000000) (106188711 / 31250000) (3398464617 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2511 / 64000) (503 / 12800) (106188711 / 31250000) (3398464617 / 1000000000) (1493677 / 40000000000) (7477933 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (106188711 / 31250000) (3398464617 / 1000000000) (1891050067 / 1000000000) (945600537 / 500000000) (1493677 / 40000000000) (7477933 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0733 :
    ∀ t ∈ Set.Icc ((503 / 12800) : ℝ) (2519 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((216352953171 / 200000000000) : ℝ) ≤ Real.exp (2 * (503 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (503 / 12800)) (216352953171 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2519 / 64000) : ℝ)) ≤ (1081899994903 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2519 / 64000)) (1081899994903 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1891200689 / 1000000000) : ℝ) ≤ Real.exp (3 * (1699231767 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1699231767 / 500000000) / 16) (1891200689 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3398889451 / 1000000000) : ℝ) / 16) ≤ (945675863 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3398889451 / 1000000000) / 16) (945675863 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((503 / 12800) : ℝ) (2519 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1699231767 / 500000000) (3398889451 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (503 / 12800) (2519 / 64000) (216352953171 / 200000000000) (1081899994903 / 1000000000000) (1699231767 / 500000000) (3398889451 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (503 / 12800) (2519 / 64000) (1699231767 / 500000000) (3398889451 / 1000000000) (37294363 / 1000000000000) (1166939 / 31250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1699231767 / 500000000) (3398889451 / 1000000000) (1891200689 / 1000000000) (945675863 / 500000000) (37294363 / 1000000000000) (1166939 / 31250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0734 :
    ∀ t ∈ Set.Icc ((2519 / 64000) : ℝ) (2523 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((540949997451 / 500000000000) : ℝ) ≤ Real.exp (2 * (2519 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2519 / 64000)) (540949997451 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2523 / 64000) : ℝ)) ≤ (216407048171 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2523 / 64000)) (216407048171 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1891351341 / 1000000000) : ℝ) ≤ Real.exp (3 * (212430523 / 62500000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (212430523 / 62500000) / 16) (1891351341 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3399314339 / 1000000000) : ℝ) / 16) ≤ (1891502409 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3399314339 / 1000000000) / 16) (1891502409 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2519 / 64000) : ℝ) (2523 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (212430523 / 62500000) (3399314339 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2519 / 64000) (2523 / 64000) (540949997451 / 500000000000) (216407048171 / 200000000000) (212430523 / 62500000) (3399314339 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2519 / 64000) (2523 / 64000) (212430523 / 62500000) (3399314339 / 1000000000) (4655857 / 125000000000) (7458897 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (212430523 / 62500000) (3399314339 / 1000000000) (1891351341 / 1000000000) (1891502409 / 1000000000) (4655857 / 125000000000) (7458897 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0735 :
    ∀ t ∈ Set.Icc ((2523 / 64000) : ℝ) (2527 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((541017620427 / 500000000000) : ℝ) ≤ Real.exp (2 * (2523 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2523 / 64000)) (541017620427 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2527 / 64000) : ℝ)) ≤ (541085251857 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2527 / 64000)) (541085251857 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((236437753 / 125000000) : ℝ) ≤ Real.exp (3 * (424914157 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (424914157 / 125000000) / 16) (236437753 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((42496741 / 12500000) : ℝ) / 16) ≤ (1891653123 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (42496741 / 12500000) / 16) (1891653123 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2523 / 64000) : ℝ) (2527 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (424914157 / 125000000) (42496741 / 12500000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2523 / 64000) (2527 / 64000) (541017620427 / 500000000000) (541085251857 / 500000000000) (424914157 / 125000000) (42496741 / 12500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2523 / 64000) (2527 / 64000) (424914157 / 125000000) (42496741 / 12500000) (37199403 / 1000000000000) (18623489 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (424914157 / 125000000) (42496741 / 12500000) (236437753 / 125000000) (1891653123 / 1000000000) (37199403 / 1000000000000) (18623489 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0736 :
    ∀ t ∈ Set.Icc ((2527 / 64000) : ℝ) (2531 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1082170503713 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2527 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2527 / 64000)) (1082170503713 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2531 / 64000) : ℝ)) ≤ (541152891741 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2531 / 64000)) (541152891741 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((945826369 / 500000000) : ℝ) ≤ Real.exp (3 * (3399738197 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3399738197 / 1000000000) / 16) (945826369 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1700082137 / 500000000) : ℝ) / 16) ≤ (472950967 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1700082137 / 500000000) / 16) (472950967 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2527 / 64000) : ℝ) (2531 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3399738197 / 1000000000) (1700082137 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2527 / 64000) (2531 / 64000) (1082170503713 / 1000000000000) (541152891741 / 500000000000) (3399738197 / 1000000000) (1700082137 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2527 / 64000) (2531 / 64000) (3399738197 / 1000000000) (1700082137 / 500000000) (9288001 / 250000000000) (1487981 / 40000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3399738197 / 1000000000) (1700082137 / 500000000) (945826369 / 500000000) (472950967 / 250000000) (9288001 / 250000000000) (1487981 / 40000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0737 :
    ∀ t ∈ Set.Icc ((2531 / 64000) : ℝ) (507 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1082305783481 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2531 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2531 / 64000)) (1082305783481 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((507 / 12800) : ℝ)) ≤ (1082441080161 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (507 / 12800)) (1082441080161 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1891803483 / 1000000000) : ℝ) ≤ Real.exp (3 * (340016319 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (340016319 / 100000000) / 16) (1891803483 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3400589321 / 1000000000) : ℝ) / 16) ≤ (472988661 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3400589321 / 1000000000) / 16) (472988661 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2531 / 64000) : ℝ) (507 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (340016319 / 100000000) (3400589321 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2531 / 64000) (507 / 12800) (1082305783481 / 1000000000000) (1082441080161 / 1000000000000) (340016319 / 100000000) (3400589321 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2531 / 64000) (507 / 12800) (340016319 / 100000000) (3400589321 / 1000000000) (1855233 / 50000000000) (18576063 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (340016319 / 100000000) (3400589321 / 1000000000) (1891803483 / 1000000000) (472988661 / 250000000) (1855233 / 50000000000) (18576063 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0738 :
    ∀ t ∈ Set.Icc ((507 / 12800) : ℝ) (2539 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((6765256751 / 6250000000) : ℝ) ≤ Real.exp (2 * (507 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (507 / 12800)) (6765256751 / 6250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2539 / 64000) : ℝ)) ≤ (1082576393753 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2539 / 64000)) (1082576393753 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1891954259 / 1000000000) : ℝ) ≤ Real.exp (3 * (3400588237 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3400588237 / 1000000000) / 16) (1891954259 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3401014421 / 1000000000) : ℝ) / 16) ≤ (1892105451 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3401014421 / 1000000000) / 16) (1892105451 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((507 / 12800) : ℝ) (2539 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3400588237 / 1000000000) (3401014421 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (507 / 12800) (2539 / 64000) (6765256751 / 6250000000) (1082576393753 / 1000000000000) (3400588237 / 1000000000) (3401014421 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (507 / 12800) (2539 / 64000) (3400588237 / 1000000000) (3401014421 / 1000000000) (37057371 / 1000000000000) (18552391 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3400588237 / 1000000000) (3401014421 / 1000000000) (1891954259 / 1000000000) (1892105451 / 1000000000) (37057371 / 1000000000000) (18552391 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0739 :
    ∀ t ∈ Set.Icc ((2539 / 64000) : ℝ) (2543 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((135322049219 / 125000000000) : ℝ) ≤ Real.exp (2 * (2539 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2539 / 64000)) (135322049219 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2543 / 64000) : ℝ)) ≤ (54135586213 / 50000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2543 / 64000)) (54135586213 / 50000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((946052533 / 500000000) : ℝ) ≤ Real.exp (3 * (1700506669 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1700506669 / 500000000) / 16) (946052533 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1700719787 / 500000000) : ℝ) / 16) ≤ (59133009 / 31250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1700719787 / 500000000) / 16) (59133009 / 31250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2539 / 64000) : ℝ) (2543 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1700506669 / 500000000) (1700719787 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2539 / 64000) (2543 / 64000) (135322049219 / 125000000000) (54135586213 / 50000000000) (1700506669 / 500000000) (1700719787 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2539 / 64000) (2543 / 64000) (1700506669 / 500000000) (1700719787 / 500000000) (4626267 / 125000000000) (37057493 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1700506669 / 500000000) (1700719787 / 500000000) (946052533 / 500000000) (59133009 / 31250000) (4626267 / 125000000000) (37057493 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch036 :
    ∀ t ∈ Set.Icc ((2463 / 64000) : ℝ) (2543 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0720
      hpThetaDensityTwoTermCompact_cell0721)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0722
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0723
      hpThetaDensityTwoTermCompact_cell0724)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0725
      hpThetaDensityTwoTermCompact_cell0726)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0727
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0728
      hpThetaDensityTwoTermCompact_cell0729))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0730
      hpThetaDensityTwoTermCompact_cell0731)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0732
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0733
      hpThetaDensityTwoTermCompact_cell0734)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0735
      hpThetaDensityTwoTermCompact_cell0736)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0737
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0738
      hpThetaDensityTwoTermCompact_cell0739)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch036
end HodgeProofHP
