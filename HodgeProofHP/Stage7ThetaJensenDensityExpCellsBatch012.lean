/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityCurvatureExponentialCells

/-! Exact rational certificates with a full infinite-series remainder bound. -/
noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell240 :
    ∀ t ∈ Set.Icc ((437 / 3200) : ℝ) (2189 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((328516123 / 250000000) : ℝ) ≤ Real.exp (2 * (437 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (437 / 3200)) (328516123 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2189 / 16000) : ℝ)) ≤ (131472169 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2189 / 16000)) (131472169 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((239042499469 / 1000000) : ℝ) ≤ Real.exp (3 * (4128133 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4128133 / 1000000)) (239042499469 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((437 / 3200) : ℝ) (2189 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4128133 / 1000000) (413033 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (437 / 3200) (2189 / 16000) (328516123 / 250000000) (131472169 / 100000000) (4128133 / 1000000) (413033 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (437 / 3200) (2189 / 16000) (4128133 / 1000000) (413033 / 100000) (43383 / 1000) (4347 / 100)
    (112929 / 1000) (57203 / 500) (-562617 / 1000) (6061 / 40000) (2328247 / 500) (53547 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4128133 / 1000000) (239042499469 / 1000000) (53547 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4128133 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4128133 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell241 :
    ∀ t ∈ Set.Icc ((2189 / 16000) : ℝ) (2193 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1314721689 / 1000000000) : ℝ) ≤ Real.exp (2 * (2189 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2189 / 16000)) (1314721689 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2193 / 16000) : ℝ)) ≤ (263075843 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2193 / 16000)) (263075843 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((240527958463 / 1000000) : ℝ) ≤ Real.exp (3 * (2065099 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2065099 / 500000)) (240527958463 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2189 / 16000) : ℝ) (2193 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2065099 / 500000) (1033099 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2189 / 16000) (2193 / 16000) (1314721689 / 1000000000) (263075843 / 200000000) (2065099 / 500000) (1033099 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2189 / 16000) (2193 / 16000) (2065099 / 500000) (1033099 / 250000) (43439 / 1000) (21763 / 500)
    (113293 / 1000) (28693 / 250) (-70298 / 125) (30163 / 200000) (2332909 / 500) (532163 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2065099 / 500000) (240527958463 / 1000000) (532163 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2065099 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2065099 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell242 :
    ∀ t ∈ Set.Icc ((2193 / 16000) : ℝ) (2197 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((657689607 / 500000000) : ℝ) ≤ Real.exp (2 * (2193 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2193 / 16000)) (657689607 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2197 / 16000) : ℝ)) ≤ (1316037069 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2197 / 16000)) (1316037069 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((4840452967 / 20000) : ℝ) ≤ Real.exp (3 * (4132263 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4132263 / 1000000)) (4840452967 / 20000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2193 / 16000) : ℝ) (2197 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4132263 / 1000000) (4134463 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2193 / 16000) (2197 / 16000) (657689607 / 500000000) (1316037069 / 1000000000) (4132263 / 1000000) (4134463 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2193 / 16000) (2197 / 16000) (4132263 / 1000000) (4134463 / 1000000) (8699 / 200) (21791 / 500)
    (113657 / 1000) (57569 / 500) (-281071 / 500) (150109 / 1000000) (116879 / 25) (1057753 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4132263 / 1000000) (4840452967 / 20000) (1057753 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4132263 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4132263 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell243 :
    ∀ t ∈ Set.Icc ((2197 / 16000) : ℝ) (2201 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((329009267 / 250000000) : ℝ) ≤ Real.exp (2 * (2197 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2197 / 16000)) (329009267 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2201 / 16000) : ℝ)) ≤ (329173813 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2201 / 16000)) (329173813 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((7610252739 / 31250) : ℝ) ≤ Real.exp (3 * (413433 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (413433 / 100000)) (7610252739 / 31250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2197 / 16000) : ℝ) (2201 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (413433 / 100000) (413653 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2197 / 16000) (2201 / 16000) (329009267 / 250000000) (329173813 / 250000000) (413433 / 100000) (413653 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2197 / 16000) (2201 / 16000) (413433 / 100000) (413653 / 100000) (43551 / 1000) (21819 / 500)
    (57011 / 500) (23101 / 200) (-561907 / 1000) (29881 / 200000) (1171129 / 250) (525607 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (413433 / 100000) (7610252739 / 31250) (525607 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (413433 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (413433 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell244 :
    ∀ t ∈ Set.Icc ((2201 / 16000) : ℝ) (441 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1316695251 / 1000000000) : ℝ) ≤ Real.exp (2 * (2201 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2201 / 16000)) (1316695251 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((441 / 3200) : ℝ)) ≤ (329338441 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (441 / 3200)) (329338441 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((245043626213 / 1000000) : ℝ) ≤ Real.exp (3 * (2068199 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2068199 / 500000)) (245043626213 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2201 / 16000) : ℝ) (441 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2068199 / 500000) (4138599 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2201 / 16000) (441 / 3200) (1316695251 / 1000000000) (329338441 / 250000000) (2068199 / 500000) (4138599 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2201 / 16000) (441 / 3200) (2068199 / 500000) (4138599 / 1000000) (43607 / 1000) (21847 / 500)
    (114389 / 1000) (115873 / 1000) (-561663 / 1000) (4647 / 31250) (586737 / 125) (130589 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2068199 / 500000) (245043626213 / 1000000) (130589 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2068199 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2068199 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell245 :
    ∀ t ∈ Set.Icc ((441 / 3200) : ℝ) (2209 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1317353763 / 1000000000) : ℝ) ≤ Real.exp (2 * (441 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (441 / 3200)) (1317353763 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2209 / 16000) : ℝ)) ≤ (659006303 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2209 / 16000)) (659006303 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((30821074539 / 125000) : ℝ) ≤ Real.exp (3 * (2069233 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2069233 / 500000)) (30821074539 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((441 / 3200) : ℝ) (2209 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2069233 / 500000) (4140669 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (441 / 3200) (2209 / 16000) (1317353763 / 1000000000) (659006303 / 500000000) (2069233 / 500000) (4140669 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (441 / 3200) (2209 / 16000) (2069233 / 500000) (4140669 / 1000000) (43663 / 1000) (175 / 4)
    (22951 / 200) (58121 / 500) (-56141 / 100) (74003 / 500000) (2351647 / 500) (1038251 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2069233 / 500000) (30821074539 / 125000) (1038251 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2069233 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2069233 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell246 :
    ∀ t ∈ Set.Icc ((2209 / 16000) : ℝ) (2213 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((263602521 / 200000000) : ℝ) ≤ Real.exp (2 * (2209 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2209 / 16000)) (263602521 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2213 / 16000) : ℝ)) ≤ (1318671777 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2213 / 16000)) (1318671777 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((124052272627 / 500000) : ℝ) ≤ Real.exp (3 * (517567 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (517567 / 125000)) (124052272627 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2209 / 16000) : ℝ) (2213 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (517567 / 125000) (207137 / 50000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2209 / 16000) (2213 / 16000) (263602521 / 200000000) (1318671777 / 1000000000) (517567 / 125000) (207137 / 50000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2209 / 16000) (2213 / 16000) (517567 / 125000) (207137 / 50000) (43719 / 1000) (21903 / 500)
    (115123 / 1000) (29153 / 250) (-280579 / 500) (147311 / 1000000) (471271 / 100) (64489 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (517567 / 125000) (124052272627 / 500000) (64489 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (517567 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (517567 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell247 :
    ∀ t ∈ Set.Icc ((2213 / 16000) : ℝ) (2217 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((41208493 / 31250000) : ℝ) ≤ Real.exp (2 * (2213 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2213 / 16000)) (41208493 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2217 / 16000) : ℝ)) ≤ (659665639 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2217 / 16000)) (659665639 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31206351371 / 125000) : ℝ) ≤ Real.exp (3 * (4142607 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4142607 / 1000000)) (31206351371 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2213 / 16000) : ℝ) (2217 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4142607 / 1000000) (1036203 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2213 / 16000) (2217 / 16000) (41208493 / 31250000) (659665639 / 500000000) (4142607 / 1000000) (1036203 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2213 / 16000) (2217 / 16000) (4142607 / 1000000) (1036203 / 250000) (1751 / 40) (43863 / 1000)
    (115491 / 1000) (58491 / 500) (-560903 / 1000) (73309 / 500000) (2361073 / 500) (1025433 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4142607 / 1000000) (31206351371 / 125000) (1025433 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4142607 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4142607 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell248 :
    ∀ t ∈ Set.Icc ((2217 / 16000) : ℝ) (2221 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1319331277 / 1000000000) : ℝ) ≤ Real.exp (2 * (2217 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2217 / 16000)) (1319331277 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2221 / 16000) : ℝ)) ≤ (329997777 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2221 / 16000)) (329997777 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((15700466691 / 62500) : ℝ) ≤ Real.exp (3 * (4144679 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4144679 / 1000000)) (15700466691 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2217 / 16000) : ℝ) (2221 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4144679 / 1000000) (829377 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2217 / 16000) (2221 / 16000) (1319331277 / 1000000000) (329997777 / 250000000) (4144679 / 1000000) (829377 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2217 / 16000) (2221 / 16000) (4144679 / 1000000) (829377 / 200000) (5479 / 125) (43919 / 1000)
    (5793 / 50) (117353 / 1000) (-140161 / 250) (18241 / 125000) (23658 / 5) (509539 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4144679 / 1000000) (15700466691 / 62500) (509539 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4144679 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4144679 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell249 :
    ∀ t ∈ Set.Icc ((2221 / 16000) : ℝ) (89 / 640), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1319991107 / 1000000000) : ℝ) ≤ Real.exp (2 * (2221 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2221 / 16000)) (1319991107 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((89 / 640) : ℝ)) ≤ (1320651269 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (89 / 640)) (1320651269 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((31596823459 / 125000) : ℝ) ≤ Real.exp (3 * (64793 / 15625)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (64793 / 15625)) (31596823459 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2221 / 16000) : ℝ) (89 / 640),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (64793 / 15625) (4148959 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2221 / 16000) (89 / 640) (1319991107 / 1000000000) (1320651269 / 1000000000) (64793 / 15625) (4148959 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2221 / 16000) (89 / 640) (64793 / 15625) (4148959 / 1000000) (5486 / 125) (1759 / 40)
    (11623 / 100) (4709 / 40) (-560381 / 1000) (145241 / 1000000) (4741073 / 1000) (1012761 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (64793 / 15625) (31596823459 / 125000) (1012761 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (64793 / 15625)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (64793 / 15625)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell250 :
    ∀ t ∈ Set.Icc ((89 / 640) : ℝ) (2229 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((330162817 / 250000000) : ℝ) ≤ Real.exp (2 * (89 / 640)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (89 / 640)) (330162817 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2229 / 16000) : ℝ)) ≤ (16516397 / 12500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2229 / 16000)) (16516397 / 12500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((254351484477 / 1000000) : ℝ) ≤ Real.exp (3 * (165953 / 40000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (165953 / 40000)) (254351484477 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((89 / 640) : ℝ) (2229 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (165953 / 40000) (2075517 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (89 / 640) (2229 / 16000) (330162817 / 250000000) (16516397 / 12500000) (165953 / 40000) (2075517 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (89 / 640) (2229 / 16000) (165953 / 40000) (2075517 / 500000) (5493 / 125) (5504 / 125)
    (116601 / 1000) (59049 / 500) (-140027 / 250) (144557 / 1000000) (1187641 / 250) (503241 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (165953 / 40000) (254351484477 / 1000000) (503241 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (165953 / 40000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (165953 / 40000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell251 :
    ∀ t ∈ Set.Icc ((2229 / 16000) : ℝ) (2233 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1321311759 / 1000000000) : ℝ) ≤ Real.exp (2 * (2229 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2229 / 16000)) (1321311759 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2233 / 16000) : ℝ)) ≤ (1321972581 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2233 / 16000)) (1321972581 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((63984938521 / 250000) : ℝ) ≤ Real.exp (3 * (41509 / 10000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (41509 / 10000)) (63984938521 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2229 / 16000) : ℝ) (2233 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (41509 / 10000) (415311 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2229 / 16000) (2233 / 16000) (1321311759 / 1000000000) (1321972581 / 1000000000) (41509 / 10000) (415311 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2229 / 16000) (2233 / 16000) (41509 / 10000) (415311 / 100000) (44001 / 1000) (5511 / 125)
    (29243 / 250) (118471 / 1000) (-279919 / 500) (35969 / 250000) (190403 / 40) (250059 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (41509 / 10000) (63984938521 / 250000) (250059 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (41509 / 10000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (41509 / 10000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell252 :
    ∀ t ∈ Set.Icc ((2233 / 16000) : ℝ) (2237 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((66098629 / 50000000) : ℝ) ≤ Real.exp (2 * (2233 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2233 / 16000)) (66098629 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2237 / 16000) : ℝ)) ≤ (330658433 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2237 / 16000)) (330658433 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((257538714013 / 1000000) : ℝ) ≤ Real.exp (3 * (259561 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (259561 / 62500)) (257538714013 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2233 / 16000) : ℝ) (2237 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (259561 / 62500) (4155187 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2233 / 16000) (2237 / 16000) (66098629 / 50000000) (330658433 / 250000000) (259561 / 62500) (4155187 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2233 / 16000) (2237 / 16000) (259561 / 62500) (4155187 / 1000000) (44057 / 1000) (8829 / 200)
    (23469 / 200) (59423 / 500) (-139891 / 250) (143197 / 1000000) (1192401 / 250) (497013 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (259561 / 62500) (257538714013 / 1000000) (497013 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (259561 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (259561 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell253 :
    ∀ t ∈ Set.Icc ((2237 / 16000) : ℝ) (2241 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1322633731 / 1000000000) : ℝ) ≤ Real.exp (2 * (2237 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2237 / 16000)) (1322633731 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2241 / 16000) : ℝ)) ≤ (661647607 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2241 / 16000)) (661647607 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8098388771 / 31250) : ℝ) ≤ Real.exp (3 * (4155053 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4155053 / 1000000)) (8098388771 / 31250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2237 / 16000) : ℝ) (2241 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4155053 / 1000000) (831453 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2237 / 16000) (2241 / 16000) (1322633731 / 1000000000) (661647607 / 500000000) (4155053 / 1000000) (831453 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2237 / 16000) (2241 / 16000) (4155053 / 1000000) (831453 / 200000) (22057 / 500) (22101 / 500)
    (58859 / 500) (119221 / 1000) (-279643 / 500) (142521 / 1000000) (597394 / 125) (987851 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4155053 / 1000000) (8098388771 / 31250) (987851 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4155053 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4155053 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell254 :
    ∀ t ∈ Set.Icc ((2241 / 16000) : ℝ) (449 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1323295213 / 1000000000) : ℝ) ≤ Real.exp (2 * (2241 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2241 / 16000)) (1323295213 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((449 / 3200) : ℝ)) ≤ (1323957027 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (449 / 3200)) (1323957027 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((52153802209 / 200000) : ℝ) ≤ Real.exp (3 * (4157131 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4157131 / 1000000)) (52153802209 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2241 / 16000) : ℝ) (449 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4157131 / 1000000) (259959 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2241 / 16000) (449 / 3200) (1323295213 / 1000000000) (1323957027 / 1000000000) (4157131 / 1000000) (259959 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2241 / 16000) (449 / 3200) (4157131 / 1000000) (259959 / 62500) (4417 / 100) (22129 / 500)
    (29523 / 250) (29899 / 250) (-139751 / 250) (17731 / 125000) (4788719 / 1000) (61357 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4157131 / 1000000) (52153802209 / 200000) (61357 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4157131 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4157131 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell255 :
    ∀ t ∈ Set.Icc ((449 / 3200) : ℝ) (2249 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((661978513 / 500000000) : ℝ) ≤ Real.exp (2 * (449 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (449 / 3200)) (661978513 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2249 / 16000) : ℝ)) ≤ (1324619171 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2249 / 16000)) (1324619171 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((32800062837 / 125000) : ℝ) ≤ Real.exp (3 * (415921 / 100000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (415921 / 100000)) (32800062837 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((449 / 3200) : ℝ) (2249 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (415921 / 100000) (260089 / 62500) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (449 / 3200) (2249 / 16000) (661978513 / 500000000) (1324619171 / 1000000000) (415921 / 100000) (260089 / 62500) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (449 / 3200) (2249 / 16000) (415921 / 100000) (260089 / 62500) (44227 / 1000) (8863 / 200)
    (59233 / 500) (119973 / 1000) (-279359 / 500) (70589 / 500000) (2399153 / 500) (121951 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (415921 / 100000) (32800062837 / 125000) (121951 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (415921 / 100000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (415921 / 100000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell256 :
    ∀ t ∈ Set.Icc ((2249 / 16000) : ℝ) (2253 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((132461917 / 100000000) : ℝ) ≤ Real.exp (2 * (2249 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2249 / 16000)) (132461917 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2253 / 16000) : ℝ)) ≤ (1325281647 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2253 / 16000)) (1325281647 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((264043785897 / 1000000) : ℝ) ≤ Real.exp (3 * (4161291 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4161291 / 1000000)) (264043785897 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2249 / 16000) : ℝ) (2253 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4161291 / 1000000) (832701 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2249 / 16000) (2253 / 16000) (132461917 / 100000000) (1325281647 / 1000000000) (4161291 / 1000000) (832701 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2249 / 16000) (2253 / 16000) (4161291 / 1000000) (832701 / 200000) (11071 / 250) (11093 / 250)
    (59421 / 500) (2407 / 20) (-279217 / 500) (14051 / 100000) (4807911 / 1000) (969537 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4161291 / 1000000) (264043785897 / 1000000) (969537 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4161291 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4161291 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell257 :
    ∀ t ∈ Set.Icc ((2253 / 16000) : ℝ) (2257 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((662640823 / 500000000) : ℝ) ≤ Real.exp (2 * (2253 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2253 / 16000)) (662640823 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2257 / 16000) : ℝ)) ≤ (1325944453 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2257 / 16000)) (1325944453 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((26569736009 / 100000) : ℝ) ≤ Real.exp (3 * (1040843 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1040843 / 250000)) (26569736009 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2253 / 16000) : ℝ) (2257 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1040843 / 250000) (1041397 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2253 / 16000) (2257 / 16000) (662640823 / 500000000) (1325944453 / 1000000000) (1040843 / 250000) (1041397 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2253 / 16000) (2257 / 16000) (1040843 / 250000) (1041397 / 250000) (44341 / 1000) (44429 / 1000)
    (59609 / 500) (120729 / 1000) (-111627 / 200) (27969 / 200000) (4817539 / 1000) (963503 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1040843 / 250000) (26569736009 / 100000) (963503 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1040843 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1040843 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell258 :
    ∀ t ∈ Set.Icc ((2257 / 16000) : ℝ) (2261 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((331486113 / 250000000) : ℝ) ≤ Real.exp (2 * (2257 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2257 / 16000)) (331486113 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2261 / 16000) : ℝ)) ≤ (1326607591 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2261 / 16000)) (1326607591 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((66840522951 / 250000) : ℝ) ≤ Real.exp (3 * (2082727 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2082727 / 500000)) (66840522951 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2257 / 16000) : ℝ) (2261 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2082727 / 500000) (4167671 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2257 / 16000) (2261 / 16000) (331486113 / 250000000) (1326607591 / 1000000000) (2082727 / 500000) (4167671 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2257 / 16000) (2261 / 16000) (2082727 / 500000) (4167671 / 1000000) (22199 / 500) (22243 / 500)
    (23919 / 200) (30277 / 250) (-557837 / 1000) (139183 / 1000000) (4827183 / 1000) (957503 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2082727 / 500000) (66840522951 / 250000) (957503 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2082727 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2082727 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell259 :
    ∀ t ∈ Set.Icc ((2261 / 16000) : ℝ) (453 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((132660759 / 100000000) : ℝ) ≤ Real.exp (2 * (2261 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2261 / 16000)) (132660759 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((453 / 3200) : ℝ)) ≤ (1327271061 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (453 / 3200)) (1327271061 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((67259515241 / 250000) : ℝ) ≤ Real.exp (3 * (4167537 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4167537 / 1000000)) (67259515241 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2261 / 16000) : ℝ) (453 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4167537 / 1000000) (833951 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (2261 / 16000) (453 / 3200) (132660759 / 100000000) (1327271061 / 1000000000) (4167537 / 1000000) (833951 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (2261 / 16000) (453 / 3200) (4167537 / 1000000) (833951 / 200000) (22227 / 500) (44543 / 1000)
    (119973 / 1000) (121487 / 1000) (-69692 / 125) (34631 / 250000) (967369 / 200) (951539 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4167537 / 1000000) (67259515241 / 250000) (951539 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4167537 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4167537 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityExpCompact_cellsBatch012 :
    ∀ t ∈ Set.Icc ((437 / 3200) : ℝ) (453 / 3200),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell240
      hpThetaDensityExpCompact_cell241)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell242
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell243
      hpThetaDensityExpCompact_cell244)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell245
      hpThetaDensityExpCompact_cell246)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell247
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell248
      hpThetaDensityExpCompact_cell249))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell250
      hpThetaDensityExpCompact_cell251)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell252
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell253
      hpThetaDensityExpCompact_cell254)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell255
      hpThetaDensityExpCompact_cell256)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell257
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell258
      hpThetaDensityExpCompact_cell259)))))

#print axioms hpThetaDensityExpCompact_cellsBatch012
end HodgeProofHP
