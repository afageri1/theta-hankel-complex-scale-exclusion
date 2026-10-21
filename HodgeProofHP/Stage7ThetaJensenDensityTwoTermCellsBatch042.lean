/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0840 :
    ∀ t ∈ Set.Icc ((3179 / 64000) : ℝ) (3187 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1104445887587 / 1000000000000) : ℝ) ≤ Real.exp (2 * (3179 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3179 / 64000)) (1104445887587 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3187 / 64000) : ℝ)) ≤ (1104722033577 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3187 / 64000)) (1104722033577 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((958318601 / 500000000) : ℝ) ≤ Real.exp (3 * (867429591 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (867429591 / 250000000) / 16) (958318601 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((27113961 / 7812500) : ℝ) / 16) ≤ (119809337 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (27113961 / 7812500) / 16) (119809337 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3179 / 64000) : ℝ) (3187 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (867429591 / 250000000) (27113961 / 7812500) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3179 / 64000) (3187 / 64000) (1104445887587 / 1000000000000) (1104722033577 / 1000000000000) (867429591 / 250000000) (27113961 / 7812500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3179 / 64000) (3187 / 64000) (867429591 / 250000000) (27113961 / 7812500) (15038331 / 500000000000) (30155143 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (867429591 / 250000000) (27113961 / 7812500) (958318601 / 500000000) (119809337 / 62500000) (15038331 / 500000000000) (30155143 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0841 :
    ∀ t ∈ Set.Icc ((3187 / 64000) : ℝ) (639 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((138090254197 / 125000000000) : ℝ) ≤ Real.exp (2 * (3187 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3187 / 64000)) (138090254197 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((639 / 12800) : ℝ)) ≤ (110499824861 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (639 / 12800)) (110499824861 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((958474497 / 500000000) : ℝ) ≤ Real.exp (3 * (1735292951 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1735292951 / 500000000) / 16) (958474497 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3471454763 / 1000000000) : ℝ) / 16) ≤ (1917261313 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3471454763 / 1000000000) / 16) (1917261313 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3187 / 64000) : ℝ) (639 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1735292951 / 500000000) (3471454763 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3187 / 64000) (639 / 12800) (138090254197 / 125000000000) (110499824861 / 100000000000) (1735292951 / 500000000) (3471454763 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3187 / 64000) (639 / 12800) (1735292951 / 500000000) (3471454763 / 1000000000) (14999233 / 500000000000) (30076763 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1735292951 / 500000000) (3471454763 / 1000000000) (958474497 / 500000000) (1917261313 / 1000000000) (14999233 / 500000000000) (30076763 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0842 :
    ∀ t ∈ Set.Icc ((639 / 12800) : ℝ) (3203 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1104998248609 / 1000000000000) : ℝ) ≤ Real.exp (2 * (639 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (639 / 12800)) (1104998248609 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3203 / 64000) : ℝ)) ≤ (1105274532707 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3203 / 64000)) (1105274532707 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((958630457 / 500000000) : ℝ) ≤ Real.exp (3 * (3471453657 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3471453657 / 1000000000) / 16) (958630457 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((217020171 / 62500000) : ℝ) / 16) ≤ (1917573363 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (217020171 / 62500000) / 16) (1917573363 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((639 / 12800) : ℝ) (3203 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3471453657 / 1000000000) (217020171 / 62500000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (639 / 12800) (3203 / 64000) (1104998248609 / 1000000000000) (1105274532707 / 1000000000000) (3471453657 / 1000000000) (217020171 / 62500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (639 / 12800) (3203 / 64000) (3471453657 / 1000000000) (217020171 / 62500000) (14960227 / 500000000000) (29998567 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3471453657 / 1000000000) (217020171 / 62500000) (958630457 / 500000000) (1917573363 / 1000000000) (14960227 / 500000000000) (29998567 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0843 :
    ∀ t ∈ Set.Icc ((3203 / 64000) : ℝ) (3211 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((552637266353 / 500000000000) : ℝ) ≤ Real.exp (2 * (3203 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3203 / 64000)) (552637266353 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3211 / 64000) : ℝ)) ≤ (552775442941 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3211 / 64000)) (552775442941 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((479393241 / 250000000) : ℝ) ≤ Real.exp (3 * (3472321629 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3472321629 / 1000000000) / 16) (479393241 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((138927637 / 40000000) : ℝ) / 16) ≤ (1917885541 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (138927637 / 40000000) / 16) (1917885541 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3203 / 64000) : ℝ) (3211 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3472321629 / 1000000000) (138927637 / 40000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3203 / 64000) (3211 / 64000) (552637266353 / 500000000000) (552775442941 / 500000000000) (3472321629 / 1000000000) (138927637 / 40000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3203 / 64000) (3211 / 64000) (3472321629 / 1000000000) (138927637 / 40000000) (14921313 / 500000000000) (5984111 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3472321629 / 1000000000) (138927637 / 40000000) (479393241 / 250000000) (1917885541 / 1000000000) (14921313 / 500000000000) (5984111 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0844 :
    ∀ t ∈ Set.Icc ((3211 / 64000) : ℝ) (3219 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1105550885881 / 1000000000000) : ℝ) ≤ Real.exp (2 * (3211 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3211 / 64000)) (1105550885881 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3219 / 64000) : ℝ)) ≤ (221165461631 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3219 / 64000)) (221165461631 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((958942571 / 500000000) : ℝ) ≤ Real.exp (3 * (1736594909 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1736594909 / 500000000) / 16) (958942571 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3474059331 / 1000000000) : ℝ) / 16) ≤ (1918197849 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3474059331 / 1000000000) / 16) (1918197849 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3211 / 64000) : ℝ) (3219 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1736594909 / 500000000) (3474059331 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3211 / 64000) (3219 / 64000) (1105550885881 / 1000000000000) (221165461631 / 200000000000) (1736594909 / 500000000) (3474059331 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3211 / 64000) (3219 / 64000) (1736594909 / 500000000) (3474059331 / 1000000000) (1488249 / 50000000000) (14921363 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1736594909 / 500000000) (3474059331 / 1000000000) (958942571 / 500000000) (1918197849 / 1000000000) (1488249 / 50000000000) (14921363 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0845 :
    ∀ t ∈ Set.Icc ((3219 / 64000) : ℝ) (3227 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((552913654077 / 500000000000) : ℝ) ≤ Real.exp (2 * (3219 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3219 / 64000)) (552913654077 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3227 / 64000) : ℝ)) ≤ (553051899771 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3227 / 64000)) (553051899771 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((38363949 / 20000000) : ℝ) ≤ Real.exp (3 * (217128639 / 62500000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (217128639 / 62500000) / 16) (38363949 / 20000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1737463977 / 500000000) : ℝ) / 16) ≤ (383702057 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1737463977 / 500000000) / 16) (383702057 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3219 / 64000) : ℝ) (3227 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (217128639 / 62500000) (1737463977 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3219 / 64000) (3227 / 64000) (552913654077 / 500000000000) (553051899771 / 500000000000) (217128639 / 62500000) (1737463977 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3219 / 64000) (3227 / 64000) (217128639 / 62500000) (1737463977 / 500000000) (14843759 / 500000000000) (744127 / 25000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (217128639 / 62500000) (1737463977 / 500000000) (38363949 / 20000000) (383702057 / 200000000) (14843759 / 500000000000) (744127 / 25000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0846 :
    ∀ t ∈ Set.Icc ((3227 / 64000) : ℝ) (647 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1106103799541 / 1000000000000) : ℝ) ≤ Real.exp (2 * (3227 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3227 / 64000)) (1106103799541 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((647 / 12800) : ℝ)) ≤ (1106380360061 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (647 / 12800)) (1106380360061 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((959254943 / 500000000) : ℝ) ≤ Real.exp (3 * (3474926847 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3474926847 / 1000000000) / 16) (959254943 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((695159359 / 200000000) : ℝ) / 16) ≤ (1918822851 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (695159359 / 200000000) / 16) (1918822851 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3227 / 64000) : ℝ) (647 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3474926847 / 1000000000) (695159359 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3227 / 64000) (647 / 12800) (1106103799541 / 1000000000000) (1106380360061 / 1000000000000) (3474926847 / 1000000000) (695159359 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3227 / 64000) (647 / 12800) (3474926847 / 1000000000) (695159359 / 200000000) (29610237 / 1000000000000) (29687617 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3474926847 / 1000000000) (695159359 / 200000000) (959254943 / 500000000) (1918822851 / 1000000000) (29610237 / 1000000000000) (29687617 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0847 :
    ∀ t ∈ Set.Icc ((647 / 12800) : ℝ) (3243 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((55319018003 / 50000000000) : ℝ) ≤ Real.exp (2 * (647 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (647 / 12800)) (55319018003 / 50000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3243 / 64000) : ℝ)) ≤ (34583030929 / 31250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3243 / 64000)) (34583030929 / 31250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1918822451 / 1000000000) : ℝ) ≤ Real.exp (3 * (434474461 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (434474461 / 125000000) / 16) (1918822451 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3476665853 / 1000000000) : ℝ) / 16) ≤ (383827109 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3476665853 / 1000000000) / 16) (383827109 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((647 / 12800) : ℝ) (3243 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (434474461 / 125000000) (3476665853 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (647 / 12800) (3243 / 64000) (55319018003 / 50000000000) (34583030929 / 31250000000) (434474461 / 125000000) (3476665853 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (647 / 12800) (3243 / 64000) (434474461 / 125000000) (3476665853 / 1000000000) (29533139 / 1000000000000) (29610337 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (434474461 / 125000000) (3476665853 / 1000000000) (1918822451 / 1000000000) (383827109 / 200000000) (29533139 / 1000000000000) (29610337 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0848 :
    ∀ t ∈ Set.Icc ((3243 / 64000) : ℝ) (3251 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1106656989727 / 1000000000000) : ℝ) ≤ Real.exp (2 * (3243 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3243 / 64000)) (1106656989727 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3251 / 64000) : ℝ)) ≤ (1106933688561 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3251 / 64000)) (1106933688561 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((383827029 / 200000000) : ℝ) ≤ Real.exp (3 * (695332949 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (695332949 / 200000000) / 16) (383827029 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((434691891 / 125000000) : ℝ) / 16) ≤ (1919448369 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (434691891 / 125000000) / 16) (1919448369 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3243 / 64000) : ℝ) (3251 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (695332949 / 200000000) (434691891 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3243 / 64000) (3251 / 64000) (1106656989727 / 1000000000000) (1106933688561 / 1000000000000) (695332949 / 200000000) (434691891 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3243 / 64000) (3251 / 64000) (695332949 / 200000000) (434691891 / 125000000) (14728111 / 500000000000) (14766619 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (695332949 / 200000000) (434691891 / 125000000) (383827029 / 200000000) (1919448369 / 1000000000) (14728111 / 500000000000) (14766619 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0849 :
    ∀ t ∈ Set.Icc ((3251 / 64000) : ℝ) (3259 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((13836671107 / 12500000000) : ℝ) ≤ Real.exp (2 * (3251 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3251 / 64000)) (13836671107 / 12500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3259 / 64000) : ℝ)) ≤ (553605228289 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3259 / 64000)) (553605228289 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1919447969 / 1000000000) : ℝ) ≤ Real.exp (3 * (173876701 / 50000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (173876701 / 50000000) / 16) (1919447969 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((173920231 / 50000000) : ℝ) / 16) ≤ (1919761321 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (173920231 / 50000000) / 16) (1919761321 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3251 / 64000) : ℝ) (3259 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (173876701 / 50000000) (173920231 / 50000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3251 / 64000) (3259 / 64000) (13836671107 / 12500000000) (553605228289 / 500000000000) (173876701 / 50000000) (173920231 / 50000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3251 / 64000) (3259 / 64000) (173876701 / 50000000) (173920231 / 50000000) (14689743 / 500000000000) (29456321 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (173876701 / 50000000) (173920231 / 50000000) (1919447969 / 1000000000) (1919761321 / 1000000000) (14689743 / 500000000000) (29456321 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0850 :
    ∀ t ∈ Set.Icc ((3259 / 64000) : ℝ) (3267 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1107210456577 / 1000000000000) : ℝ) ≤ Real.exp (2 * (3259 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3259 / 64000)) (1107210456577 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3267 / 64000) : ℝ)) ≤ (221497458759 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3267 / 64000)) (221497458759 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1919760921 / 1000000000) : ℝ) ≤ Real.exp (3 * (434800439 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (434800439 / 125000000) / 16) (1919760921 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((347927433 / 100000000) : ℝ) / 16) ≤ (480018601 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (347927433 / 100000000) / 16) (480018601 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3259 / 64000) : ℝ) (3267 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (434800439 / 125000000) (347927433 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3259 / 64000) (3267 / 64000) (1107210456577 / 1000000000000) (221497458759 / 200000000000) (434800439 / 125000000) (347927433 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3259 / 64000) (3267 / 64000) (434800439 / 125000000) (347927433 / 100000000) (29302931 / 1000000000000) (5875917 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (434800439 / 125000000) (347927433 / 100000000) (1919760921 / 1000000000) (480018601 / 250000000) (29302931 / 1000000000000) (5875917 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0851 :
    ∀ t ∈ Set.Icc ((3267 / 64000) : ℝ) (131 / 2560), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((553743646897 / 500000000000) : ℝ) ≤ Real.exp (2 * (3267 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3267 / 64000)) (553743646897 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((131 / 2560) : ℝ)) ≤ (1107764200231 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (131 / 2560)) (1107764200231 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((480018501 / 250000000) : ℝ) ≤ Real.exp (3 * (1739636611 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1739636611 / 500000000) / 16) (480018501 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1740072129 / 500000000) : ℝ) / 16) ≤ (384077523 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1740072129 / 500000000) / 16) (384077523 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3267 / 64000) : ℝ) (131 / 2560),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1739636611 / 500000000) (1740072129 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3267 / 64000) (131 / 2560) (553743646897 / 500000000000) (1107764200231 / 1000000000000) (1739636611 / 500000000) (1740072129 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3267 / 64000) (131 / 2560) (1739636611 / 500000000) (1740072129 / 500000000) (29226557 / 1000000000000) (2930303 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1739636611 / 500000000) (1740072129 / 500000000) (480018501 / 250000000) (384077523 / 200000000) (29226557 / 1000000000000) (2930303 / 100000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0852 :
    ∀ t ∈ Set.Icc ((131 / 2560) : ℝ) (3283 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((110776420023 / 100000000000) : ℝ) ≤ Real.exp (2 * (131 / 2560)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (131 / 2560)) (110776420023 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3283 / 64000) : ℝ)) ≤ (1108041175901 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3283 / 64000)) (1108041175901 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((384077443 / 200000000) : ℝ) ≤ Real.exp (3 * (3480143149 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3480143149 / 1000000000) / 16) (384077443 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1740507201 / 500000000) : ℝ) / 16) ≤ (480175239 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1740507201 / 500000000) / 16) (480175239 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((131 / 2560) : ℝ) (3283 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3480143149 / 1000000000) (1740507201 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (131 / 2560) (3283 / 64000) (110776420023 / 100000000000) (1108041175901 / 1000000000000) (3480143149 / 1000000000) (1740507201 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (131 / 2560) (3283 / 64000) (3480143149 / 1000000000) (1740507201 / 500000000) (14575181 / 500000000000) (5845331 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3480143149 / 1000000000) (1740507201 / 500000000) (384077443 / 200000000) (480175239 / 250000000) (14575181 / 500000000000) (5845331 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0853 :
    ∀ t ∈ Set.Icc ((3283 / 64000) : ℝ) (3291 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((11080411759 / 10000000000) : ℝ) ≤ Real.exp (2 * (3283 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3283 / 64000)) (11080411759 / 10000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3291 / 64000) : ℝ)) ≤ (44332728833 / 40000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3291 / 64000)) (44332728833 / 40000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((480175139 / 250000000) : ℝ) ≤ Real.exp (3 * (3481013293 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3481013293 / 1000000000) / 16) (480175139 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((696376953 / 200000000) : ℝ) / 16) ≤ (1921014427 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (696376953 / 200000000) / 16) (1921014427 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3283 / 64000) : ℝ) (3291 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3481013293 / 1000000000) (696376953 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3283 / 64000) (3291 / 64000) (11080411759 / 10000000000) (44332728833 / 40000000000) (3481013293 / 1000000000) (696376953 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3283 / 64000) (3291 / 64000) (3481013293 / 1000000000) (696376953 / 200000000) (29074347 / 1000000000000) (1457523 / 50000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3481013293 / 1000000000) (696376953 / 200000000) (480175139 / 250000000) (1921014427 / 1000000000) (29074347 / 1000000000000) (1457523 / 50000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0854 :
    ∀ t ∈ Set.Icc ((3291 / 64000) : ℝ) (3299 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((138539777603 / 125000000000) : ℝ) ≤ Real.exp (2 * (3291 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3291 / 64000)) (138539777603 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3299 / 64000) : ℝ)) ≤ (554297667509 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3299 / 64000)) (554297667509 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((960507013 / 500000000) : ℝ) ≤ Real.exp (3 * (696376731 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (696376731 / 200000000) / 16) (960507013 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((696551069 / 200000000) : ℝ) / 16) ≤ (1921328027 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (696551069 / 200000000) / 16) (1921328027 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3291 / 64000) : ℝ) (3299 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (696376731 / 200000000) (696551069 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3291 / 64000) (3299 / 64000) (138539777603 / 125000000000) (554297667509 / 500000000000) (696376731 / 200000000) (696551069 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3291 / 64000) (3299 / 64000) (696376731 / 200000000) (696551069 / 200000000) (28998511 / 1000000000000) (5814889 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (696376731 / 200000000) (696551069 / 200000000) (960507013 / 500000000) (1921328027 / 1000000000) (28998511 / 1000000000000) (5814889 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0855 :
    ∀ t ∈ Set.Icc ((3299 / 64000) : ℝ) (3307 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1108595335017 / 1000000000000) : ℝ) ≤ Real.exp (2 * (3299 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3299 / 64000)) (1108595335017 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3307 / 64000) : ℝ)) ≤ (554436259249 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3307 / 64000)) (554436259249 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((960663813 / 500000000) : ℝ) ≤ Real.exp (3 * (696550847 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (696550847 / 200000000) / 16) (960663813 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3483626143 / 1000000000) : ℝ) / 16) ≤ (480410439 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3483626143 / 1000000000) / 16) (480410439 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3299 / 64000) : ℝ) (3307 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (696550847 / 200000000) (3483626143 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3299 / 64000) (3307 / 64000) (1108595335017 / 1000000000000) (554436259249 / 500000000000) (696550847 / 200000000) (3483626143 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3299 / 64000) (3307 / 64000) (696550847 / 200000000) (3483626143 / 1000000000) (5784571 / 200000000000) (28998609 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (696550847 / 200000000) (3483626143 / 1000000000) (960663813 / 500000000) (480410439 / 250000000) (5784571 / 200000000000) (28998609 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0856 :
    ∀ t ∈ Set.Icc ((3307 / 64000) : ℝ) (663 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1108872518497 / 1000000000000) : ℝ) ≤ Real.exp (2 * (3307 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3307 / 64000)) (1108872518497 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((663 / 12800) : ℝ)) ≤ (1109149771283 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (663 / 12800)) (1109149771283 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((384328271 / 200000000) : ℝ) ≤ Real.exp (3 * (3483625033 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3483625033 / 1000000000) / 16) (384328271 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1742248579 / 500000000) : ℝ) / 16) ≤ (384391123 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1742248579 / 500000000) / 16) (384391123 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3307 / 64000) : ℝ) (663 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3483625033 / 1000000000) (1742248579 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3307 / 64000) (663 / 12800) (1108872518497 / 1000000000000) (1109149771283 / 1000000000000) (3483625033 / 1000000000) (1742248579 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3307 / 64000) (663 / 12800) (3483625033 / 1000000000) (1742248579 / 500000000) (28847377 / 1000000000000) (3615369 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3483625033 / 1000000000) (1742248579 / 500000000) (384328271 / 200000000) (384391123 / 200000000) (28847377 / 1000000000000) (3615369 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0857 :
    ∀ t ∈ Set.Icc ((663 / 12800) : ℝ) (3323 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((554574885641 / 500000000000) : ℝ) ≤ Real.exp (2 * (663 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (663 / 12800)) (554574885641 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3323 / 64000) : ℝ)) ≤ (1109427093389 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3323 / 64000)) (1109427093389 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((960977607 / 500000000) : ℝ) ≤ Real.exp (3 * (217781003 / 62500000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (217781003 / 62500000) / 16) (960977607 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3485368391 / 1000000000) : ℝ) / 16) ≤ (480567401 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3485368391 / 1000000000) / 16) (480567401 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((663 / 12800) : ℝ) (3323 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (217781003 / 62500000) (3485368391 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (663 / 12800) (3323 / 64000) (554574885641 / 500000000000) (1109427093389 / 1000000000000) (217781003 / 62500000) (3485368391 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (663 / 12800) (3323 / 64000) (217781003 / 62500000) (3485368391 / 1000000000) (28772077 / 1000000000000) (14423737 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (217781003 / 62500000) (3485368391 / 1000000000) (960977607 / 500000000) (480567401 / 250000000) (28772077 / 1000000000000) (14423737 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0858 :
    ∀ t ∈ Set.Icc ((3323 / 64000) : ℝ) (3331 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((277356773347 / 250000000000) : ℝ) ≤ Real.exp (2 * (3323 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3323 / 64000)) (277356773347 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3331 / 64000) : ℝ)) ≤ (221940896967 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3331 / 64000)) (221940896967 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1922269203 / 1000000000) : ℝ) ≤ Real.exp (3 * (3485367281 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3485367281 / 1000000000) / 16) (1922269203 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1743119921 / 500000000) : ℝ) / 16) ≤ (1922583723 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1743119921 / 500000000) / 16) (1922583723 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3323 / 64000) : ℝ) (3331 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3485367281 / 1000000000) (1743119921 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3323 / 64000) (3331 / 64000) (277356773347 / 250000000000) (221940896967 / 200000000000) (3485367281 / 1000000000) (1743119921 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3323 / 64000) (3331 / 64000) (3485367281 / 1000000000) (1743119921 / 500000000) (5739391 / 200000000000) (14386087 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3485367281 / 1000000000) (1743119921 / 500000000) (1922269203 / 1000000000) (1922583723 / 1000000000) (5739391 / 200000000000) (14386087 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0859 :
    ∀ t ∈ Set.Icc ((3331 / 64000) : ℝ) (3339 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((554852242417 / 500000000000) : ℝ) ≤ Real.exp (2 * (3331 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3331 / 64000)) (554852242417 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3339 / 64000) : ℝ)) ≤ (1109981945637 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3339 / 64000)) (1109981945637 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((961291661 / 500000000) : ℝ) ≤ Real.exp (3 * (3486238731 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3486238731 / 1000000000) / 16) (961291661 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3487111511 / 1000000000) : ℝ) / 16) ≤ (480724493 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3487111511 / 1000000000) / 16) (480724493 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3331 / 64000) : ℝ) (3339 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3486238731 / 1000000000) (3487111511 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3331 / 64000) (3339 / 64000) (554852242417 / 500000000000) (1109981945637 / 1000000000000) (3486238731 / 1000000000) (3487111511 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3331 / 64000) (3339 / 64000) (3486238731 / 1000000000) (3487111511 / 1000000000) (2862201 / 100000000000) (7174263 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3486238731 / 1000000000) (3487111511 / 1000000000) (961291661 / 500000000) (480724493 / 250000000) (2862201 / 100000000000) (7174263 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch042 :
    ∀ t ∈ Set.Icc ((3179 / 64000) : ℝ) (3339 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0840
      hpThetaDensityTwoTermCompact_cell0841)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0842
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0843
      hpThetaDensityTwoTermCompact_cell0844)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0845
      hpThetaDensityTwoTermCompact_cell0846)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0847
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0848
      hpThetaDensityTwoTermCompact_cell0849))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0850
      hpThetaDensityTwoTermCompact_cell0851)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0852
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0853
      hpThetaDensityTwoTermCompact_cell0854)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0855
      hpThetaDensityTwoTermCompact_cell0856)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0857
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0858
      hpThetaDensityTwoTermCompact_cell0859)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch042
end HodgeProofHP
