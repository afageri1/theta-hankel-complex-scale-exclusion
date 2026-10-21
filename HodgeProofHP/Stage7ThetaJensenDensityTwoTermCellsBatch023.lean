/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0460 :
    ∀ t ∈ Set.Icc ((353 / 12800) : ℝ) (1767 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((264176428011 / 250000000000) : ℝ) ≤ Real.exp (2 * (353 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (353 / 12800)) (264176428011 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1767 / 64000) : ℝ)) ≤ (132096469777 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1767 / 64000)) (132096469777 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1863489703 / 1000000000) : ℝ) ≤ Real.exp (3 * (3319738211 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3319738211 / 1000000000) / 16) (1863489703 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3319946759 / 1000000000) : ℝ) / 16) ≤ (1863562573 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3319946759 / 1000000000) / 16) (1863562573 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((353 / 12800) : ℝ) (1767 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3319738211 / 1000000000) (3319946759 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (353 / 12800) (1767 / 64000) (264176428011 / 250000000000) (132096469777 / 125000000000) (3319738211 / 1000000000) (3319946759 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (353 / 12800) (1767 / 64000) (3319738211 / 1000000000) (3319946759 / 1000000000) (47260283 / 1000000000000) (23644931 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3319738211 / 1000000000) (3319946759 / 1000000000) (1863489703 / 1000000000) (1863562573 / 1000000000) (47260283 / 1000000000000) (23644931 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0461 :
    ∀ t ∈ Set.Icc ((1767 / 64000) : ℝ) (1769 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((211354351643 / 200000000000) : ℝ) ≤ Real.exp (2 * (1767 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1767 / 64000)) (211354351643 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1769 / 64000) : ℝ)) ≤ (211367561703 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1769 / 64000)) (211367561703 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((931781101 / 500000000) : ℝ) ≤ Real.exp (3 * (3319945701 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3319945701 / 1000000000) / 16) (931781101 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1660077131 / 500000000) : ℝ) / 16) ≤ (46590877 / 25000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1660077131 / 500000000) / 16) (46590877 / 25000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1767 / 64000) : ℝ) (1769 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3319945701 / 1000000000) (1660077131 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1767 / 64000) (1769 / 64000) (211354351643 / 200000000000) (211367561703 / 200000000000) (3319945701 / 1000000000) (1660077131 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1767 / 64000) (1769 / 64000) (3319945701 / 1000000000) (1660077131 / 500000000) (5903859 / 125000000000) (9452087 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3319945701 / 1000000000) (1660077131 / 500000000) (931781101 / 500000000) (46590877 / 25000000) (5903859 / 125000000000) (9452087 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0462 :
    ∀ t ∈ Set.Icc ((1769 / 64000) : ℝ) (1771 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((528418904257 / 500000000000) : ℝ) ≤ Real.exp (2 * (1769 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1769 / 64000)) (528418904257 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1771 / 64000) : ℝ)) ≤ (528451931471 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1771 / 64000)) (528451931471 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1863634709 / 1000000000) : ℝ) ≤ Real.exp (3 * (830038301 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (830038301 / 250000000) / 16) (1863634709 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1660180889 / 500000000) : ℝ) / 16) ≤ (931853797 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1660180889 / 500000000) / 16) (931853797 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1769 / 64000) : ℝ) (1771 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (830038301 / 250000000) (1660180889 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1769 / 64000) (1771 / 64000) (528418904257 / 500000000000) (528451931471 / 500000000000) (830038301 / 250000000) (1660180889 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1769 / 64000) (1771 / 64000) (830038301 / 250000000) (1660180889 / 500000000) (23600739 / 500000000000) (2951939 / 62500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (830038301 / 250000000) (1660180889 / 500000000) (1863634709 / 1000000000) (931853797 / 500000000) (23600739 / 500000000000) (2951939 / 62500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0463 :
    ∀ t ∈ Set.Icc ((1771 / 64000) : ℝ) (1773 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1056903862941 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1771 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1771 / 64000)) (1056903862941 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1773 / 64000) : ℝ)) ≤ (528484960749 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1773 / 64000)) (528484960749 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1863707223 / 1000000000) : ℝ) ≤ Real.exp (3 * (41504509 / 12500000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (41504509 / 12500000) / 16) (1863707223 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3320569307 / 1000000000) : ℝ) / 16) ≤ (372756023 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3320569307 / 1000000000) / 16) (372756023 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1771 / 64000) : ℝ) (1773 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (41504509 / 12500000) (3320569307 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1771 / 64000) (1773 / 64000) (1056903862941 / 1000000000000) (528484960749 / 500000000000) (41504509 / 12500000) (3320569307 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1771 / 64000) (1773 / 64000) (41504509 / 12500000) (3320569307 / 1000000000) (471721 / 10000000000) (47201629 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (41504509 / 12500000) (3320569307 / 1000000000) (1863707223 / 1000000000) (372756023 / 200000000) (471721 / 10000000000) (47201629 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0464 :
    ∀ t ∈ Set.Icc ((1773 / 64000) : ℝ) (71 / 2560), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1056969921497 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1773 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1773 / 64000)) (1056969921497 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((71 / 2560) : ℝ)) ≤ (528517992091 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (71 / 2560)) (528517992091 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((58243117 / 31250000) : ℝ) ≤ Real.exp (3 * (3320568249 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3320568249 / 1000000000) / 16) (58243117 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3320776849 / 1000000000) : ℝ) / 16) ≤ (465963161 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3320776849 / 1000000000) / 16) (465963161 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1773 / 64000) : ℝ) (71 / 2560),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3320568249 / 1000000000) (3320776849 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1773 / 64000) (71 / 2560) (1056969921497 / 1000000000000) (528517992091 / 500000000000) (3320568249 / 1000000000) (3320776849 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1773 / 64000) (71 / 2560) (3320568249 / 1000000000) (3320776849 / 1000000000) (47142739 / 1000000000000) (11793063 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3320568249 / 1000000000) (3320776849 / 1000000000) (58243117 / 31250000) (465963161 / 250000000) (47142739 / 1000000000000) (11793063 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0465 :
    ∀ t ∈ Set.Icc ((71 / 2560) : ℝ) (1777 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1057035984181 / 1000000000000) : ℝ) ≤ Real.exp (2 * (71 / 2560)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (71 / 2560)) (1057035984181 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1777 / 64000) : ℝ)) ≤ (264275512749 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1777 / 64000)) (264275512749 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1863852273 / 1000000000) : ℝ) ≤ Real.exp (3 * (3320775791 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3320775791 / 1000000000) / 16) (1863852273 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((830246101 / 250000000) : ℝ) / 16) ≤ (93196259 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (830246101 / 250000000) / 16) (93196259 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((71 / 2560) : ℝ) (1777 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3320775791 / 1000000000) (830246101 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (71 / 2560) (1777 / 64000) (1057035984181 / 1000000000000) (264275512749 / 250000000000) (3320775791 / 1000000000) (830246101 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (71 / 2560) (1777 / 64000) (3320775791 / 1000000000) (830246101 / 250000000) (23556697 / 500000000000) (4714289 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3320775791 / 1000000000) (830246101 / 250000000) (1863852273 / 1000000000) (93196259 / 50000000) (23556697 / 500000000000) (4714289 / 100000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0466 :
    ∀ t ∈ Set.Icc ((1777 / 64000) : ℝ) (1779 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((211420410199 / 200000000000) : ℝ) ≤ Real.exp (2 * (1777 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1777 / 64000)) (211420410199 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1779 / 64000) : ℝ)) ≤ (1057168121939 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1779 / 64000)) (1057168121939 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1863924809 / 1000000000) : ℝ) ≤ Real.exp (3 * (1660491673 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1660491673 / 500000000) / 16) (1863924809 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((830297993 / 250000000) : ℝ) / 16) ≤ (465999431 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (830297993 / 250000000) / 16) (465999431 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1777 / 64000) : ℝ) (1779 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1660491673 / 500000000) (830297993 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1777 / 64000) (1779 / 64000) (211420410199 / 200000000000) (1057168121939 / 1000000000000) (1660491673 / 500000000) (830297993 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1777 / 64000) (1779 / 64000) (1660491673 / 500000000) (830297993 / 250000000) (9416813 / 200000000000) (9422709 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1660491673 / 500000000) (830297993 / 250000000) (1863924809 / 1000000000) (465999431 / 250000000) (9416813 / 200000000000) (9422709 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0467 :
    ∀ t ∈ Set.Icc ((1779 / 64000) : ℝ) (1781 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((528584060969 / 500000000000) : ℝ) ≤ Real.exp (2 * (1779 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1779 / 64000)) (528584060969 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1781 / 64000) : ℝ)) ≤ (1057234197011 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1781 / 64000)) (1057234197011 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1863997353 / 1000000000) : ℝ) ≤ Real.exp (3 * (1660595457 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1660595457 / 500000000) / 16) (1863997353 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3321399553 / 1000000000) : ℝ) / 16) ≤ (932035137 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3321399553 / 1000000000) / 16) (932035137 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1779 / 64000) : ℝ) (1781 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1660595457 / 500000000) (3321399553 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1779 / 64000) (1781 / 64000) (528584060969 / 500000000000) (1057234197011 / 1000000000000) (1660595457 / 500000000) (3321399553 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1779 / 64000) (1781 / 64000) (1660595457 / 500000000) (3321399553 / 1000000000) (47054753 / 1000000000000) (5885527 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1660595457 / 500000000) (3321399553 / 1000000000) (1863997353 / 1000000000) (932035137 / 500000000) (47054753 / 1000000000000) (5885527 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0468 :
    ∀ t ∈ Set.Icc ((1781 / 64000) : ℝ) (1783 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((105723419701 / 100000000000) : ℝ) ≤ Real.exp (2 * (1781 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1781 / 64000)) (105723419701 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1783 / 64000) : ℝ)) ≤ (1057300276213 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1783 / 64000)) (1057300276213 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((116504369 / 62500000) : ℝ) ≤ Real.exp (3 * (664279699 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (664279699 / 200000000) / 16) (116504369 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3321607147 / 1000000000) : ℝ) / 16) ≤ (1864142833 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3321607147 / 1000000000) / 16) (1864142833 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1781 / 64000) : ℝ) (1783 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (664279699 / 200000000) (3321607147 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1781 / 64000) (1783 / 64000) (105723419701 / 100000000000) (1057300276213 / 1000000000000) (664279699 / 200000000) (3321607147 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1781 / 64000) (1783 / 64000) (664279699 / 200000000) (3321607147 / 1000000000) (47025457 / 1000000000000) (5881863 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (664279699 / 200000000) (3321607147 / 1000000000) (116504369 / 62500000) (1864142833 / 1000000000) (47025457 / 1000000000000) (5881863 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0469 :
    ∀ t ∈ Set.Icc ((1783 / 64000) : ℝ) (357 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((264325069053 / 250000000000) : ℝ) ≤ Real.exp (2 * (1783 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1783 / 64000)) (264325069053 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((357 / 12800) : ℝ)) ≤ (528683179773 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (357 / 12800)) (528683179773 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((932071231 / 500000000) : ℝ) ≤ Real.exp (3 * (3321606089 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3321606089 / 1000000000) / 16) (932071231 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1660907377 / 500000000) : ℝ) / 16) ≤ (932107699 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1660907377 / 500000000) / 16) (932107699 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1783 / 64000) : ℝ) (357 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3321606089 / 1000000000) (1660907377 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1783 / 64000) (357 / 12800) (264325069053 / 250000000000) (528683179773 / 500000000000) (3321606089 / 1000000000) (1660907377 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1783 / 64000) (357 / 12800) (3321606089 / 1000000000) (1660907377 / 500000000) (23498089 / 500000000000) (5878201 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3321606089 / 1000000000) (1660907377 / 500000000) (932071231 / 500000000) (932107699 / 500000000) (23498089 / 500000000000) (5878201 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0470 :
    ∀ t ∈ Set.Icc ((357 / 12800) : ℝ) (1787 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((211473271909 / 200000000000) : ℝ) ≤ Real.exp (2 * (357 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (357 / 12800)) (211473271909 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1787 / 64000) : ℝ)) ≤ (33044763969 / 31250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1787 / 64000)) (33044763969 / 31250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((466053757 / 250000000) : ℝ) ≤ Real.exp (3 * (51903339 / 15625000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (51903339 / 15625000) / 16) (466053757 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1661011187 / 500000000) : ℝ) / 16) ≤ (1864287971 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1661011187 / 500000000) / 16) (1864287971 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((357 / 12800) : ℝ) (1787 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (51903339 / 15625000) (1661011187 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (357 / 12800) (1787 / 64000) (211473271909 / 200000000000) (33044763969 / 31250000000) (51903339 / 15625000) (1661011187 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (357 / 12800) (1787 / 64000) (51903339 / 15625000) (1661011187 / 500000000) (9393383 / 200000000000) (5874541 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (51903339 / 15625000) (1661011187 / 500000000) (466053757 / 250000000) (1864287971 / 1000000000) (9393383 / 200000000000) (5874541 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0471 :
    ∀ t ∈ Set.Icc ((1787 / 64000) : ℝ) (1789 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1057432447007 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1787 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1787 / 64000)) (1057432447007 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1789 / 64000) : ℝ)) ≤ (528749269301 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1789 / 64000)) (528749269301 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1864287601 / 1000000000) : ℝ) ≤ Real.exp (3 * (830505329 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (830505329 / 250000000) / 16) (1864287601 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3322230007 / 1000000000) : ℝ) / 16) ≤ (233045069 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3322230007 / 1000000000) / 16) (233045069 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1787 / 64000) : ℝ) (1789 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (830505329 / 250000000) (3322230007 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1787 / 64000) (1789 / 64000) (1057432447007 / 1000000000000) (528749269301 / 500000000000) (830505329 / 250000000) (3322230007 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1787 / 64000) (1789 / 64000) (830505329 / 250000000) (3322230007 / 1000000000) (46937669 / 1000000000000) (9393413 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (830505329 / 250000000) (3322230007 / 1000000000) (1864287601 / 1000000000) (233045069 / 125000000) (46937669 / 1000000000000) (9393413 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0472 :
    ∀ t ∈ Set.Icc ((1789 / 64000) : ℝ) (1791 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1057498538601 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1789 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1789 / 64000)) (1057498538601 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1791 / 64000) : ℝ)) ≤ (528782317163 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1791 / 64000)) (528782317163 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((93218009 / 50000000) : ℝ) ≤ Real.exp (3 * (830557237 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (830557237 / 250000000) / 16) (93218009 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3322437653 / 1000000000) : ℝ) / 16) ≤ (1864433139 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3322437653 / 1000000000) / 16) (1864433139 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1789 / 64000) : ℝ) (1791 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (830557237 / 250000000) (3322437653 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1789 / 64000) (1791 / 64000) (1057498538601 / 1000000000000) (528782317163 / 500000000000) (830557237 / 250000000) (3322437653 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1789 / 64000) (1791 / 64000) (830557237 / 250000000) (3322437653 / 1000000000) (46908439 / 1000000000000) (46937819 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (830557237 / 250000000) (3322437653 / 1000000000) (93218009 / 50000000) (1864433139 / 1000000000) (46908439 / 1000000000000) (46937819 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0473 :
    ∀ t ∈ Set.Icc ((1791 / 64000) : ℝ) (1793 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((42302585373 / 40000000000) : ℝ) ≤ Real.exp (2 * (1791 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1791 / 64000)) (42302585373 / 40000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1793 / 64000) : ℝ)) ≤ (1057630734181 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1793 / 64000)) (1057630734181 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((14565881 / 7812500) : ℝ) ≤ Real.exp (3 * (1661218297 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1661218297 / 500000000) / 16) (14565881 / 7812500) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((51916333 / 15625000) : ℝ) / 16) ≤ (372901147 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (51916333 / 15625000) / 16) (372901147 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1791 / 64000) : ℝ) (1793 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1661218297 / 500000000) (51916333 / 15625000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1791 / 64000) (1793 / 64000) (42302585373 / 40000000000) (1057630734181 / 1000000000000) (1661218297 / 500000000) (51916333 / 15625000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1791 / 64000) (1793 / 64000) (1661218297 / 500000000) (51916333 / 15625000) (1875169 / 40000000000) (46908589 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1661218297 / 500000000) (51916333 / 15625000) (14565881 / 7812500) (372901147 / 200000000) (1875169 / 40000000000) (46908589 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0474 :
    ∀ t ∈ Set.Icc ((1793 / 64000) : ℝ) (359 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((52881536709 / 50000000000) : ℝ) ≤ Real.exp (2 * (1793 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1793 / 64000)) (52881536709 / 50000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((359 / 12800) : ℝ)) ≤ (132212104771 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (359 / 12800)) (132212104771 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1864505363 / 1000000000) : ℝ) ≤ Real.exp (3 * (3322644253 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3322644253 / 1000000000) / 16) (1864505363 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3322852983 / 1000000000) : ℝ) / 16) ≤ (1864578337 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3322852983 / 1000000000) / 16) (1864578337 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1793 / 64000) : ℝ) (359 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3322644253 / 1000000000) (3322852983 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1793 / 64000) (359 / 12800) (52881536709 / 50000000000) (132212104771 / 125000000000) (3322644253 / 1000000000) (3322852983 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1793 / 64000) (359 / 12800) (3322644253 / 1000000000) (3322852983 / 1000000000) (46850027 / 1000000000000) (75007 / 1600000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3322644253 / 1000000000) (3322852983 / 1000000000) (1864505363 / 1000000000) (1864578337 / 1000000000) (46850027 / 1000000000000) (75007 / 1600000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0475 :
    ∀ t ∈ Set.Icc ((359 / 12800) : ℝ) (1797 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1057696838167 / 1000000000000) : ℝ) ≤ Real.exp (2 * (359 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (359 / 12800)) (1057696838167 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1797 / 64000) : ℝ)) ≤ (528881473143 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1797 / 64000)) (528881473143 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((932288983 / 500000000) : ℝ) ≤ Real.exp (3 * (132914077 / 40000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (132914077 / 40000000) / 16) (932288983 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((830765167 / 250000000) : ℝ) / 16) ≤ (932325473 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (830765167 / 250000000) / 16) (932325473 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((359 / 12800) : ℝ) (1797 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (132914077 / 40000000) (830765167 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (359 / 12800) (1797 / 64000) (1057696838167 / 1000000000000) (528881473143 / 500000000000) (132914077 / 40000000) (830765167 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (359 / 12800) (1797 / 64000) (132914077 / 40000000) (830765167 / 250000000) (46820847 / 1000000000000) (46850177 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (132914077 / 40000000) (830765167 / 250000000) (932288983 / 500000000) (932325473 / 500000000) (46820847 / 1000000000000) (46850177 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0476 :
    ∀ t ∈ Set.Icc ((1797 / 64000) : ℝ) (1799 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((211552589257 / 200000000000) : ℝ) ≤ Real.exp (2 * (1797 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1797 / 64000)) (211552589257 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1799 / 64000) : ℝ)) ≤ (132228632317 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1799 / 64000)) (132228632317 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((74586023 / 40000000) : ℝ) ≤ Real.exp (3 * (3323059609 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3323059609 / 1000000000) / 16) (74586023 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1661634183 / 500000000) : ℝ) / 16) ≤ (466180891 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1661634183 / 500000000) / 16) (466180891 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1797 / 64000) : ℝ) (1799 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3323059609 / 1000000000) (1661634183 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1797 / 64000) (1799 / 64000) (211552589257 / 200000000000) (132228632317 / 125000000000) (3323059609 / 1000000000) (1661634183 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1797 / 64000) (1799 / 64000) (3323059609 / 1000000000) (1661634183 / 500000000) (23395841 / 500000000000) (46820997 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3323059609 / 1000000000) (1661634183 / 500000000) (74586023 / 40000000) (466180891 / 250000000) (23395841 / 500000000000) (46820997 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0477 :
    ∀ t ∈ Set.Icc ((1799 / 64000) : ℝ) (1801 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((211565811707 / 200000000000) : ℝ) ≤ Real.exp (2 * (1799 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1799 / 64000)) (211565811707 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1801 / 64000) : ℝ)) ≤ (528947587459 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1801 / 64000)) (528947587459 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((233090399 / 125000000) : ℝ) ≤ Real.exp (3 * (3323267307 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3323267307 / 1000000000) / 16) (233090399 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3323476077 / 1000000000) : ℝ) / 16) ≤ (466199047 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3323476077 / 1000000000) / 16) (466199047 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1799 / 64000) : ℝ) (1801 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3323267307 / 1000000000) (3323476077 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1799 / 64000) (1801 / 64000) (211565811707 / 200000000000) (528947587459 / 500000000000) (3323267307 / 1000000000) (3323476077 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1799 / 64000) (1801 / 64000) (3323267307 / 1000000000) (3323476077 / 1000000000) (46762533 / 1000000000000) (5848979 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3323267307 / 1000000000) (3323476077 / 1000000000) (233090399 / 125000000) (466199047 / 250000000) (46762533 / 1000000000000) (5848979 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0478 :
    ∀ t ∈ Set.Icc ((1801 / 64000) : ℝ) (1803 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1057895174917 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1801 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1801 / 64000)) (1057895174917 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1803 / 64000) : ℝ)) ≤ (1057961295433 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1803 / 64000)) (1057961295433 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1864795817 / 1000000000) : ℝ) ≤ Real.exp (3 * (1661737509 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1661737509 / 500000000) / 16) (1864795817 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3323683801 / 1000000000) : ℝ) / 16) ≤ (93243441 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3323683801 / 1000000000) / 16) (93243441 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1801 / 64000) : ℝ) (1803 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1661737509 / 500000000) (3323683801 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1801 / 64000) (1803 / 64000) (1057895174917 / 1000000000000) (1057961295433 / 1000000000000) (1661737509 / 500000000) (3323683801 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1801 / 64000) (1803 / 64000) (1661737509 / 500000000) (3323683801 / 1000000000) (46733401 / 1000000000000) (46762683 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1661737509 / 500000000) (3323683801 / 1000000000) (1864795817 / 1000000000) (93243441 / 50000000) (46733401 / 1000000000000) (46762683 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0479 :
    ∀ t ∈ Set.Icc ((1803 / 64000) : ℝ) (361 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((132245161929 / 125000000000) : ℝ) ≤ Real.exp (2 * (1803 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1803 / 64000)) (132245161929 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((361 / 12800) : ℝ)) ≤ (13225342751 / 12500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (361 / 12800)) (13225342751 / 12500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1864868449 / 1000000000) : ℝ) ≤ Real.exp (3 * (1661841371 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1661841371 / 500000000) / 16) (1864868449 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3323891537 / 1000000000) : ℝ) / 16) ≤ (1864941459 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3323891537 / 1000000000) / 16) (1864941459 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1803 / 64000) : ℝ) (361 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1661841371 / 500000000) (3323891537 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1803 / 64000) (361 / 12800) (132245161929 / 125000000000) (13225342751 / 12500000000) (1661841371 / 500000000) (3323891537 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1803 / 64000) (361 / 12800) (1661841371 / 500000000) (3323891537 / 1000000000) (23352143 / 500000000000) (46733551 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1661841371 / 500000000) (3323891537 / 1000000000) (1864868449 / 1000000000) (1864941459 / 1000000000) (23352143 / 500000000000) (46733551 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch023 :
    ∀ t ∈ Set.Icc ((353 / 12800) : ℝ) (361 / 12800),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0460
      hpThetaDensityTwoTermCompact_cell0461)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0462
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0463
      hpThetaDensityTwoTermCompact_cell0464)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0465
      hpThetaDensityTwoTermCompact_cell0466)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0467
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0468
      hpThetaDensityTwoTermCompact_cell0469))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0470
      hpThetaDensityTwoTermCompact_cell0471)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0472
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0473
      hpThetaDensityTwoTermCompact_cell0474)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0475
      hpThetaDensityTwoTermCompact_cell0476)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0477
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0478
      hpThetaDensityTwoTermCompact_cell0479)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch023
end HodgeProofHP
