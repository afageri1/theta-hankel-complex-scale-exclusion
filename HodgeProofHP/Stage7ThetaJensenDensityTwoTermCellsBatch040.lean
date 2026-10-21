/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0800 :
    ∀ t ∈ Set.Icc ((2859 / 64000) : ℝ) (2867 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((109345646739 / 100000000000) : ℝ) ≤ Real.exp (2 * (2859 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2859 / 64000)) (109345646739 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2867 / 64000) : ℝ)) ≤ (1093729865681 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2867 / 64000)) (1093729865681 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((952135151 / 500000000) : ℝ) ≤ Real.exp (3 * (343519409 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (343519409 / 100000000) / 16) (952135151 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((343605409 / 100000000) : ℝ) / 16) ≤ (1904577391 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (343605409 / 100000000) / 16) (1904577391 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2859 / 64000) : ℝ) (2867 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (343519409 / 100000000) (343605409 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2859 / 64000) (2867 / 64000) (109345646739 / 100000000000) (1093729865681 / 1000000000000) (343519409 / 100000000) (343605409 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2859 / 64000) (2867 / 64000) (343519409 / 100000000) (343605409 / 100000000) (3335969 / 100000000000) (3344587 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (343519409 / 100000000) (343605409 / 100000000) (952135151 / 500000000) (1904577391 / 1000000000) (3335969 / 100000000000) (3344587 / 100000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0801 :
    ∀ t ∈ Set.Icc ((2867 / 64000) : ℝ) (23 / 512), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((13671623321 / 12500000000) : ℝ) ≤ Real.exp (2 * (2867 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2867 / 64000)) (13671623321 / 12500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((23 / 512) : ℝ)) ≤ (109400333233 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (23 / 512)) (109400333233 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1904577 / 1000000) : ℝ) ≤ Real.exp (3 * (859013249 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (859013249 / 250000000) / 16) (1904577 / 1000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3436913211 / 1000000000) : ℝ) / 16) ≤ (380976843 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3436913211 / 1000000000) / 16) (380976843 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2867 / 64000) : ℝ) (23 / 512),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (859013249 / 250000000) (3436913211 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2867 / 64000) (23 / 512) (13671623321 / 12500000000) (109400333233 / 100000000000) (859013249 / 250000000) (3436913211 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2867 / 64000) (23 / 512) (859013249 / 250000000) (3436913211 / 1000000000) (1663691 / 50000000000) (166799 / 5000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (859013249 / 250000000) (3436913211 / 1000000000) (1904577 / 1000000) (380976843 / 200000000) (1663691 / 50000000000) (166799 / 5000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0802 :
    ∀ t ∈ Set.Icc ((23 / 512) : ℝ) (2883 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1094003332329 / 1000000000000) : ℝ) ≤ Real.exp (2 * (23 / 512)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (23 / 512)) (1094003332329 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2883 / 64000) : ℝ)) ≤ (1094276867353 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2883 / 64000)) (1094276867353 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1904883823 / 1000000000) : ℝ) ≤ Real.exp (3 * (859228029 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (859228029 / 250000000) / 16) (1904883823 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3437772547 / 1000000000) : ℝ) / 16) ≤ (381038233 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3437772547 / 1000000000) / 16) (381038233 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((23 / 512) : ℝ) (2883 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (859228029 / 250000000) (3437772547 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (23 / 512) (2883 / 64000) (1094003332329 / 1000000000000) (1094276867353 / 1000000000000) (859228029 / 250000000) (3437772547 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (23 / 512) (2883 / 64000) (859228029 / 250000000) (3437772547 / 1000000000) (33188151 / 1000000000000) (33273931 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (859228029 / 250000000) (3437772547 / 1000000000) (1904883823 / 1000000000) (381038233 / 200000000) (33188151 / 1000000000000) (33273931 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0803 :
    ∀ t ∈ Set.Icc ((2883 / 64000) : ℝ) (2891 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((136784608419 / 125000000000) : ℝ) ≤ Real.exp (2 * (2883 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2883 / 64000)) (136784608419 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2891 / 64000) : ℝ)) ≤ (1094550470769 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2891 / 64000)) (1094550470769 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1905190773 / 1000000000) : ℝ) ≤ Real.exp (3 * (859442863 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (859442863 / 250000000) / 16) (1905190773 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1719316049 / 500000000) : ℝ) / 16) ≤ (952749121 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1719316049 / 500000000) / 16) (952749121 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2883 / 64000) : ℝ) (2891 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (859442863 / 250000000) (1719316049 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2883 / 64000) (2891 / 64000) (136784608419 / 125000000000) (1094550470769 / 1000000000000) (859442863 / 250000000) (1719316049 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2883 / 64000) (2891 / 64000) (859442863 / 250000000) (1719316049 / 500000000) (827567 / 25000000000) (33188261 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (859442863 / 250000000) (1719316049 / 500000000) (1905190773 / 1000000000) (952749121 / 500000000) (827567 / 25000000000) (33188261 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0804 :
    ∀ t ∈ Set.Icc ((2891 / 64000) : ℝ) (2899 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((68409404423 / 62500000000) : ℝ) ≤ Real.exp (2 * (2891 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2891 / 64000)) (68409404423 / 62500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2899 / 64000) : ℝ)) ≤ (547412071297 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2899 / 64000)) (547412071297 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1905497849 / 1000000000) : ℝ) ≤ Real.exp (3 * (1719315501 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1719315501 / 500000000) / 16) (1905497849 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3439491863 / 1000000000) : ℝ) / 16) ≤ (476451361 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3439491863 / 1000000000) / 16) (476451361 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2891 / 64000) : ℝ) (2899 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1719315501 / 500000000) (3439491863 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2891 / 64000) (2899 / 64000) (68409404423 / 62500000000) (547412071297 / 500000000000) (1719315501 / 500000000) (3439491863 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2891 / 64000) (2899 / 64000) (1719315501 / 500000000) (3439491863 / 1000000000) (515897 / 15625000000) (3310279 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1719315501 / 500000000) (3439491863 / 1000000000) (1905497849 / 1000000000) (476451361 / 250000000) (515897 / 15625000000) (3310279 / 100000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0805 :
    ∀ t ∈ Set.Icc ((2899 / 64000) : ℝ) (2907 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1094824142593 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2899 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2899 / 64000)) (1094824142593 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2907 / 64000) : ℝ)) ≤ (547548941423 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2907 / 64000)) (547548941423 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((476451263 / 250000000) : ℝ) ≤ Real.exp (3 * (3439490767 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3439490767 / 1000000000) / 16) (476451263 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((860087961 / 250000000) : ℝ) / 16) ≤ (1906112773 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (860087961 / 250000000) / 16) (1906112773 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2899 / 64000) : ℝ) (2907 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3439490767 / 1000000000) (860087961 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2899 / 64000) (2907 / 64000) (1094824142593 / 1000000000000) (547548941423 / 500000000000) (3439490767 / 1000000000) (860087961 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2899 / 64000) (2907 / 64000) (3439490767 / 1000000000) (860087961 / 250000000) (6586467 / 200000000000) (16508759 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3439490767 / 1000000000) (860087961 / 250000000) (476451263 / 250000000) (1906112773 / 1000000000) (6586467 / 200000000000) (16508759 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0806 :
    ∀ t ∈ Set.Icc ((2907 / 64000) : ℝ) (583 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((219019576569 / 200000000000) : ℝ) ≤ Real.exp (2 * (2907 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2907 / 64000)) (219019576569 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((583 / 12800) : ℝ)) ≤ (547685845771 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (583 / 12800)) (547685845771 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((95305619 / 50000000) : ℝ) ≤ Real.exp (3 * (3440350747 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3440350747 / 1000000000) / 16) (95305619 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3441212039 / 1000000000) : ℝ) / 16) ≤ (476605057 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3441212039 / 1000000000) / 16) (476605057 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2907 / 64000) : ℝ) (583 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3440350747 / 1000000000) (3441212039 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2907 / 64000) (583 / 12800) (219019576569 / 200000000000) (547685845771 / 500000000000) (3440350747 / 1000000000) (3441212039 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2907 / 64000) (583 / 12800) (3440350747 / 1000000000) (3441212039 / 1000000000) (1642373 / 50000000000) (6586489 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3440350747 / 1000000000) (3441212039 / 1000000000) (95305619 / 50000000) (476605057 / 250000000) (1642373 / 50000000000) (6586489 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0807 :
    ∀ t ∈ Set.Icc ((583 / 12800) : ℝ) (2923 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1095371691541 / 1000000000000) : ℝ) ≤ Real.exp (2 * (583 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (583 / 12800)) (1095371691541 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2923 / 64000) : ℝ)) ≤ (547822784349 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2923 / 64000)) (547822784349 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((476604959 / 250000000) : ℝ) ≤ Real.exp (3 * (3441210943 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3441210943 / 1000000000) / 16) (476604959 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((68841449 / 20000000) : ℝ) / 16) ≤ (190672781 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (68841449 / 20000000) / 16) (190672781 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((583 / 12800) : ℝ) (2923 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3441210943 / 1000000000) (68841449 / 20000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (583 / 12800) (2923 / 64000) (1095371691541 / 1000000000000) (547822784349 / 500000000000) (3441210943 / 1000000000) (68841449 / 20000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (583 / 12800) (2923 / 64000) (3441210943 / 1000000000) (68841449 / 20000000) (32762783 / 1000000000000) (32847569 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3441210943 / 1000000000) (68841449 / 20000000) (476604959 / 250000000) (190672781 / 100000000) (32762783 / 1000000000000) (32847569 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0808 :
    ∀ t ∈ Set.Icc ((2923 / 64000) : ℝ) (2931 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1095645568697 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2923 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2923 / 64000)) (1095645568697 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2931 / 64000) : ℝ)) ≤ (273979878583 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2931 / 64000)) (273979878583 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1906727417 / 1000000000) : ℝ) ≤ Real.exp (3 * (3442071353 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3442071353 / 1000000000) / 16) (1906727417 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((137717323 / 40000000) : ℝ) / 16) ≤ (1907035519 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (137717323 / 40000000) / 16) (1907035519 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2923 / 64000) : ℝ) (2931 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3442071353 / 1000000000) (137717323 / 40000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2923 / 64000) (2931 / 64000) (1095645568697 / 1000000000000) (273979878583 / 250000000000) (3442071353 / 1000000000) (137717323 / 40000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2923 / 64000) (2931 / 64000) (3442071353 / 1000000000) (137717323 / 40000000) (16339151 / 500000000000) (8190723 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3442071353 / 1000000000) (137717323 / 40000000) (1906727417 / 1000000000) (1907035519 / 1000000000) (16339151 / 500000000000) (8190723 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0809 :
    ∀ t ∈ Set.Icc ((2931 / 64000) : ℝ) (2939 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1095919514331 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2931 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2931 / 64000)) (1095919514331 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2939 / 64000) : ℝ)) ≤ (1096193528461 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2939 / 64000)) (1096193528461 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((15256281 / 8000000) : ℝ) ≤ Real.exp (3 * (1721465989 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1721465989 / 500000000) / 16) (15256281 / 8000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((860948479 / 250000000) : ℝ) / 16) ≤ (953671677 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (860948479 / 250000000) / 16) (953671677 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2931 / 64000) : ℝ) (2939 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1721465989 / 500000000) (860948479 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2931 / 64000) (2939 / 64000) (1095919514331 / 1000000000000) (1096193528461 / 1000000000000) (1721465989 / 500000000) (860948479 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2931 / 64000) (2939 / 64000) (1721465989 / 500000000) (860948479 / 250000000) (16297009 / 500000000000) (32678411 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1721465989 / 500000000) (860948479 / 250000000) (15256281 / 8000000) (953671677 / 500000000) (16297009 / 500000000000) (32678411 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0810 :
    ∀ t ∈ Set.Icc ((2939 / 64000) : ℝ) (2947 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((54809676423 / 50000000000) : ℝ) ≤ Real.exp (2 * (2939 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2939 / 64000)) (54809676423 / 50000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2947 / 64000) : ℝ)) ≤ (548233805551 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2947 / 64000)) (548233805551 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((23841787 / 12500000) : ℝ) ≤ Real.exp (3 * (3443792819 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3443792819 / 1000000000) / 16) (23841787 / 12500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((861163743 / 250000000) : ℝ) / 16) ≤ (381530263 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (861163743 / 250000000) / 16) (381530263 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2939 / 64000) : ℝ) (2947 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3443792819 / 1000000000) (861163743 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2939 / 64000) (2947 / 64000) (54809676423 / 50000000000) (548233805551 / 500000000000) (3443792819 / 1000000000) (861163743 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2939 / 64000) (2947 / 64000) (3443792819 / 1000000000) (861163743 / 250000000) (32509931 / 1000000000000) (32594127 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3443792819 / 1000000000) (861163743 / 250000000) (23841787 / 12500000) (381530263 / 200000000) (32509931 / 1000000000000) (32594127 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0811 :
    ∀ t ∈ Set.Icc ((2947 / 64000) : ℝ) (591 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1096467611101 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2947 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2947 / 64000)) (1096467611101 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((591 / 12800) : ℝ)) ≤ (34273180071 / 31250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (591 / 12800)) (34273180071 / 31250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((953825461 / 500000000) : ℝ) ≤ Real.exp (3 * (27557231 / 8000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (27557231 / 8000000) / 16) (953825461 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((861379061 / 250000000) : ℝ) / 16) ≤ (476989851 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (861379061 / 250000000) / 16) (476989851 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2947 / 64000) : ℝ) (591 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (27557231 / 8000000) (861379061 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2947 / 64000) (591 / 12800) (1096467611101 / 1000000000000) (34273180071 / 31250000000) (27557231 / 8000000) (861379061 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2947 / 64000) (591 / 12800) (27557231 / 8000000) (861379061 / 250000000) (810651 / 25000000000) (812751 / 25000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (27557231 / 8000000) (861379061 / 250000000) (953825461 / 500000000) (476989851 / 250000000) (810651 / 25000000000) (812751 / 25000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0812 :
    ∀ t ∈ Set.Icc ((591 / 12800) : ℝ) (2963 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1096741762271 / 1000000000000) : ℝ) ≤ Real.exp (2 * (591 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (591 / 12800)) (1096741762271 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2963 / 64000) : ℝ)) ≤ (274253995497 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2963 / 64000)) (274253995497 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((190795901 / 100000000) : ℝ) ≤ Real.exp (3 * (1722757573 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1722757573 / 500000000) / 16) (190795901 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((344637773 / 100000000) : ℝ) / 16) ≤ (1908267619 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (344637773 / 100000000) / 16) (1908267619 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((591 / 12800) : ℝ) (2963 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1722757573 / 500000000) (344637773 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (591 / 12800) (2963 / 64000) (1096741762271 / 1000000000000) (274253995497 / 250000000000) (1722757573 / 500000000) (344637773 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (591 / 12800) (2963 / 64000) (1722757573 / 500000000) (344637773 / 100000000) (6468469 / 200000000000) (8106537 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1722757573 / 500000000) (344637773 / 100000000) (190795901 / 100000000) (1908267619 / 1000000000) (6468469 / 200000000000) (8106537 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0813 :
    ∀ t ∈ Set.Icc ((2963 / 64000) : ℝ) (2971 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1097015981987 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2963 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2963 / 64000)) (1097015981987 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2971 / 64000) : ℝ)) ≤ (274322567567 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2971 / 64000)) (274322567567 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((76330689 / 40000000) : ℝ) ≤ Real.exp (3 * (430797079 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (430797079 / 125000000) / 16) (76330689 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3447239433 / 1000000000) : ℝ) / 16) ≤ (1908575961 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3447239433 / 1000000000) / 16) (1908575961 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2963 / 64000) : ℝ) (2971 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (430797079 / 125000000) (3447239433 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2963 / 64000) (2971 / 64000) (1097015981987 / 1000000000000) (274322567567 / 250000000000) (430797079 / 125000000) (3447239433 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2963 / 64000) (2971 / 64000) (430797079 / 125000000) (3447239433 / 1000000000) (8064711 / 250000000000) (8085613 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (430797079 / 125000000) (3447239433 / 1000000000) (76330689 / 40000000) (1908575961 / 1000000000) (8064711 / 250000000000) (8085613 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0814 :
    ∀ t ∈ Set.Icc ((2971 / 64000) : ℝ) (2979 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1097290270267 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2971 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2971 / 64000)) (1097290270267 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2979 / 64000) : ℝ)) ≤ (1097564627129 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2979 / 64000)) (1097564627129 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1908575567 / 1000000000) : ℝ) ≤ Real.exp (3 * (1723619167 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1723619167 / 500000000) / 16) (1908575567 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((68962027 / 20000000) : ℝ) / 16) ≤ (190888443 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (68962027 / 20000000) / 16) (190888443 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2971 / 64000) : ℝ) (2979 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1723619167 / 500000000) (68962027 / 20000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2971 / 64000) (2979 / 64000) (1097290270267 / 1000000000000) (1097564627129 / 1000000000000) (1723619167 / 500000000) (68962027 / 20000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2971 / 64000) (2979 / 64000) (1723619167 / 500000000) (68962027 / 20000000) (16087769 / 500000000000) (4032369 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1723619167 / 500000000) (68962027 / 20000000) (1908575567 / 1000000000) (190888443 / 100000000) (16087769 / 500000000000) (4032369 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0815 :
    ∀ t ∈ Set.Icc ((2979 / 64000) : ℝ) (2987 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((137195578391 / 125000000000) : ℝ) ≤ Real.exp (2 * (2979 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2979 / 64000)) (137195578391 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2987 / 64000) : ℝ)) ≤ (274459763147 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2987 / 64000)) (274459763147 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((477221009 / 250000000) : ℝ) ≤ Real.exp (3 * (862025063 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (862025063 / 250000000) / 16) (477221009 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3448963483 / 1000000000) : ℝ) / 16) ≤ (954596513 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3448963483 / 1000000000) / 16) (954596513 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2979 / 64000) : ℝ) (2987 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (862025063 / 250000000) (3448963483 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2979 / 64000) (2987 / 64000) (137195578391 / 125000000000) (274459763147 / 250000000000) (862025063 / 250000000) (3448963483 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2979 / 64000) (2987 / 64000) (862025063 / 250000000) (3448963483 / 1000000000) (32092427 / 1000000000000) (16087823 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (862025063 / 250000000) (3448963483 / 1000000000) (477221009 / 250000000) (954596513 / 500000000) (32092427 / 1000000000000) (16087823 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0816 :
    ∀ t ∈ Set.Icc ((2987 / 64000) : ℝ) (599 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1097839052587 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2987 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2987 / 64000)) (1097839052587 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((599 / 12800) : ℝ)) ≤ (1098113546661 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (599 / 12800)) (1098113546661 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((238649079 / 125000000) : ℝ) ≤ Real.exp (3 * (215560149 / 62500000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (215560149 / 62500000) / 16) (238649079 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((431228229 / 125000000) : ℝ) / 16) ≤ (1909501749 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (431228229 / 125000000) / 16) (1909501749 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2987 / 64000) : ℝ) (599 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (215560149 / 62500000) (431228229 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2987 / 64000) (599 / 12800) (1097839052587 / 1000000000000) (1098113546661 / 1000000000000) (215560149 / 62500000) (431228229 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2987 / 64000) (599 / 12800) (215560149 / 62500000) (431228229 / 125000000) (3200951 / 100000000000) (16046267 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (215560149 / 62500000) (431228229 / 125000000) (238649079 / 125000000) (1909501749 / 1000000000) (3200951 / 100000000000) (16046267 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0817 :
    ∀ t ∈ Set.Icc ((599 / 12800) : ℝ) (3003 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((54905677333 / 50000000000) : ℝ) ≤ Real.exp (2 * (599 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (599 / 12800)) (54905677333 / 50000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3003 / 64000) : ℝ)) ≤ (1098388109367 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3003 / 64000)) (1098388109367 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((381900271 / 200000000) : ℝ) ≤ Real.exp (3 * (3449824733 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3449824733 / 1000000000) / 16) (381900271 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((862672099 / 250000000) : ℝ) / 16) ≤ (1909810599 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (862672099 / 250000000) / 16) (1909810599 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((599 / 12800) : ℝ) (3003 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3449824733 / 1000000000) (862672099 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (599 / 12800) (3003 / 64000) (54905677333 / 50000000000) (1098388109367 / 1000000000000) (3449824733 / 1000000000) (862672099 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (599 / 12800) (3003 / 64000) (3449824733 / 1000000000) (862672099 / 250000000) (15963393 / 500000000000) (32009617 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3449824733 / 1000000000) (862672099 / 250000000) (381900271 / 200000000) (1909810599 / 1000000000) (15963393 / 500000000000) (32009617 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0818 :
    ∀ t ∈ Set.Icc ((3003 / 64000) : ℝ) (3011 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((549194054683 / 500000000000) : ℝ) ≤ Real.exp (2 * (3003 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3003 / 64000)) (549194054683 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3011 / 64000) : ℝ)) ≤ (549331370361 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3011 / 64000)) (549331370361 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((381962041 / 200000000) : ℝ) ≤ Real.exp (3 * (3450687297 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3450687297 / 1000000000) / 16) (381962041 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((431443897 / 125000000) : ℝ) / 16) ≤ (1910119577 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (431443897 / 125000000) / 16) (1910119577 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3003 / 64000) : ℝ) (3011 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3450687297 / 1000000000) (431443897 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3003 / 64000) (3011 / 64000) (549194054683 / 500000000000) (549331370361 / 500000000000) (3450687297 / 1000000000) (431443897 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3003 / 64000) (3011 / 64000) (3450687297 / 1000000000) (431443897 / 125000000) (995133 / 31250000000) (31926893 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3450687297 / 1000000000) (431443897 / 125000000) (381962041 / 200000000) (1910119577 / 1000000000) (995133 / 31250000000) (31926893 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0819 :
    ∀ t ∈ Set.Icc ((3011 / 64000) : ℝ) (3019 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1098662740721 / 1000000000000) : ℝ) ≤ Real.exp (2 * (3011 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3011 / 64000)) (1098662740721 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3019 / 64000) : ℝ)) ≤ (1098937440743 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3019 / 64000)) (1098937440743 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((955059591 / 500000000) : ℝ) ≤ Real.exp (3 * (862887519 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (862887519 / 250000000) / 16) (955059591 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((863103543 / 250000000) : ℝ) / 16) ≤ (955214341 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (863103543 / 250000000) / 16) (955214341 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3011 / 64000) : ℝ) (3019 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (862887519 / 250000000) (863103543 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3011 / 64000) (3019 / 64000) (1098662740721 / 1000000000000) (1098937440743 / 1000000000000) (862887519 / 250000000) (863103543 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3011 / 64000) (3019 / 64000) (862887519 / 250000000) (863103543 / 250000000) (15880959 / 500000000000) (15922181 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (862887519 / 250000000) (863103543 / 250000000) (955059591 / 500000000) (955214341 / 500000000) (15880959 / 500000000000) (15922181 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch040 :
    ∀ t ∈ Set.Icc ((2859 / 64000) : ℝ) (3019 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0800
      hpThetaDensityTwoTermCompact_cell0801)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0802
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0803
      hpThetaDensityTwoTermCompact_cell0804)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0805
      hpThetaDensityTwoTermCompact_cell0806)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0807
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0808
      hpThetaDensityTwoTermCompact_cell0809))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0810
      hpThetaDensityTwoTermCompact_cell0811)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0812
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0813
      hpThetaDensityTwoTermCompact_cell0814)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0815
      hpThetaDensityTwoTermCompact_cell0816)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0817
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0818
      hpThetaDensityTwoTermCompact_cell0819)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch040
end HodgeProofHP
