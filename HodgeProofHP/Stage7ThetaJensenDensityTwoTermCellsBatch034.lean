/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0680 :
    ∀ t ∈ Set.Icc ((2303 / 64000) : ℝ) (2307 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1074621761609 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2303 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2303 / 64000)) (1074621761609 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2307 / 64000) : ℝ)) ≤ (537378048863 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2307 / 64000)) (537378048863 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((376652007 / 200000000) : ℝ) ≤ Real.exp (3 * (3376023129 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3376023129 / 1000000000) / 16) (376652007 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1688223117 / 500000000) : ℝ) / 16) ≤ (376681889 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1688223117 / 500000000) / 16) (376681889 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2303 / 64000) : ℝ) (2307 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3376023129 / 1000000000) (1688223117 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2303 / 64000) (2307 / 64000) (1074621761609 / 1000000000000) (537378048863 / 500000000000) (3376023129 / 1000000000) (1688223117 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2303 / 64000) (2307 / 64000) (3376023129 / 1000000000) (1688223117 / 500000000) (19945921 / 500000000000) (39942511 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3376023129 / 1000000000) (1688223117 / 500000000) (376652007 / 200000000) (376681889 / 200000000) (19945921 / 500000000000) (39942511 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0681 :
    ∀ t ∈ Set.Icc ((2307 / 64000) : ℝ) (2311 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((42990243909 / 40000000000) : ℝ) ≤ Real.exp (2 * (2307 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2307 / 64000)) (42990243909 / 40000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2311 / 64000) : ℝ)) ≤ (214978090127 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2311 / 64000)) (214978090127 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((235426133 / 125000000) : ℝ) ≤ Real.exp (3 * (1688222579 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1688222579 / 500000000) / 16) (235426133 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((844217079 / 250000000) : ℝ) / 16) ≤ (376711701 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (844217079 / 250000000) / 16) (376711701 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2307 / 64000) : ℝ) (2311 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1688222579 / 500000000) (844217079 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2307 / 64000) (2311 / 64000) (42990243909 / 40000000000) (214978090127 / 200000000000) (1688222579 / 500000000) (844217079 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2307 / 64000) (2311 / 64000) (1688222579 / 500000000) (844217079 / 250000000) (39841361 / 1000000000000) (9972993 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1688222579 / 500000000) (844217079 / 250000000) (235426133 / 125000000) (376711701 / 200000000) (39841361 / 1000000000000) (9972993 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0682 :
    ∀ t ∈ Set.Icc ((2311 / 64000) : ℝ) (463 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((537445225317 / 500000000000) : ℝ) ≤ Real.exp (2 * (2311 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2311 / 64000)) (537445225317 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((463 / 12800) : ℝ)) ≤ (1075024820339 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (463 / 12800)) (1075024820339 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((470889531 / 250000000) : ℝ) ≤ Real.exp (3 * (84421681 / 25000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (84421681 / 25000000) / 16) (470889531 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3377290451 / 1000000000) : ℝ) / 16) ≤ (376741519 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3377290451 / 1000000000) / 16) (376741519 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2311 / 64000) : ℝ) (463 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (84421681 / 25000000) (3377290451 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2311 / 64000) (463 / 12800) (537445225317 / 500000000000) (1075024820339 / 1000000000000) (84421681 / 25000000) (3377290451 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2311 / 64000) (463 / 12800) (84421681 / 25000000) (3377290451 / 1000000000) (19895469 / 500000000000) (39841491 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (84421681 / 25000000) (3377290451 / 1000000000) (470889531 / 250000000) (376741519 / 200000000) (19895469 / 500000000000) (39841491 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0683 :
    ∀ t ∈ Set.Icc ((463 / 12800) : ℝ) (2319 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((537512410169 / 500000000000) : ℝ) ≤ Real.exp (2 * (463 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (463 / 12800)) (537512410169 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2319 / 64000) : ℝ)) ≤ (26878980171 / 25000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2319 / 64000)) (26878980171 / 25000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((941853607 / 500000000) : ℝ) ≤ Real.exp (3 * (5403663 / 1600000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (5403663 / 1600000) / 16) (941853607 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3377712639 / 1000000000) : ℝ) / 16) ≤ (470964179 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3377712639 / 1000000000) / 16) (470964179 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((463 / 12800) : ℝ) (2319 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (5403663 / 1600000) (3377712639 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (463 / 12800) (2319 / 64000) (537512410169 / 500000000000) (26878980171 / 25000000000) (5403663 / 1600000) (3377712639 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (463 / 12800) (2319 / 64000) (5403663 / 1600000) (3377712639 / 1000000000) (9935143 / 250000000000) (39791067 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (5403663 / 1600000) (3377712639 / 1000000000) (941853607 / 500000000) (470964179 / 250000000) (9935143 / 250000000000) (39791067 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0684 :
    ∀ t ∈ Set.Icc ((2319 / 64000) : ℝ) (2323 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1075159206839 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2319 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2319 / 64000)) (1075159206839 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2323 / 64000) : ℝ)) ≤ (1075293610141 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2323 / 64000)) (1075293610141 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((941928167 / 500000000) : ℝ) ≤ Real.exp (3 * (1688855781 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1688855781 / 500000000) / 16) (941928167 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3378134879 / 1000000000) : ℝ) / 16) ≤ (1884005867 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3378134879 / 1000000000) / 16) (1884005867 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2319 / 64000) : ℝ) (2323 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1688855781 / 500000000) (3378134879 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2319 / 64000) (2323 / 64000) (1075159206839 / 1000000000000) (1075293610141 / 1000000000000) (1688855781 / 500000000) (3378134879 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2319 / 64000) (2323 / 64000) (1688855781 / 500000000) (3378134879 / 1000000000) (39690263 / 1000000000000) (19870351 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1688855781 / 500000000) (3378134879 / 1000000000) (941928167 / 500000000) (1884005867 / 1000000000) (39690263 / 1000000000000) (19870351 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0685 :
    ∀ t ∈ Set.Icc ((2323 / 64000) : ℝ) (2327 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((53764680507 / 50000000000) : ℝ) ≤ Real.exp (2 * (2323 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2323 / 64000)) (53764680507 / 50000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2327 / 64000) : ℝ)) ≤ (268857007561 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2327 / 64000)) (268857007561 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((942002743 / 500000000) : ℝ) ≤ Real.exp (3 * (3378133803 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3378133803 / 1000000000) / 16) (942002743 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((844639293 / 250000000) : ℝ) / 16) ≤ (235519381 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (844639293 / 250000000) / 16) (235519381 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2323 / 64000) : ℝ) (2327 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3378133803 / 1000000000) (844639293 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2323 / 64000) (2327 / 64000) (53764680507 / 50000000000) (268857007561 / 250000000000) (3378133803 / 1000000000) (844639293 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2323 / 64000) (2327 / 64000) (3378133803 / 1000000000) (844639293 / 250000000) (39640013 / 1000000000000) (39690393 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3378133803 / 1000000000) (844639293 / 250000000) (942002743 / 500000000) (235519381 / 125000000) (39640013 / 1000000000000) (39690393 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0686 :
    ∀ t ∈ Set.Icc ((2327 / 64000) : ℝ) (2331 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1075428030243 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2327 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2327 / 64000)) (1075428030243 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2331 / 64000) : ℝ)) ≤ (21511249343 / 20000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2331 / 64000)) (21511249343 / 20000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1884154667 / 1000000000) : ℝ) ≤ Real.exp (3 * (52789939 / 15625000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (52789939 / 15625000) / 16) (1884154667 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1689489759 / 500000000) : ℝ) / 16) ≤ (94215213 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1689489759 / 500000000) / 16) (94215213 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2327 / 64000) : ℝ) (2331 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (52789939 / 15625000) (1689489759 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2327 / 64000) (2331 / 64000) (1075428030243 / 1000000000000) (21511249343 / 20000000000) (52789939 / 15625000) (1689489759 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2327 / 64000) (2331 / 64000) (52789939 / 15625000) (1689489759 / 500000000) (39589819 / 1000000000000) (19820071 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (52789939 / 15625000) (1689489759 / 500000000) (1884154667 / 1000000000) (94215213 / 50000000) (39589819 / 1000000000000) (19820071 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0687 :
    ∀ t ∈ Set.Icc ((2331 / 64000) : ℝ) (467 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1075562467149 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2331 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2331 / 64000)) (1075562467149 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((467 / 12800) : ℝ)) ≤ (1075696920861 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (467 / 12800)) (1075696920861 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1884303879 / 1000000000) : ℝ) ≤ Real.exp (3 * (1689489221 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1689489221 / 500000000) / 16) (1884303879 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3379401917 / 1000000000) : ℝ) / 16) ≤ (942226751 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3379401917 / 1000000000) / 16) (942226751 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2331 / 64000) : ℝ) (467 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1689489221 / 500000000) (3379401917 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2331 / 64000) (467 / 12800) (1075562467149 / 1000000000000) (1075696920861 / 1000000000000) (1689489221 / 500000000) (3379401917 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2331 / 64000) (467 / 12800) (1689489221 / 500000000) (3379401917 / 1000000000) (39539683 / 1000000000000) (9897487 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1689489221 / 500000000) (3379401917 / 1000000000) (1884303879 / 1000000000) (942226751 / 500000000) (39539683 / 1000000000000) (9897487 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0688 :
    ∀ t ∈ Set.Icc ((467 / 12800) : ℝ) (2339 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((53784846043 / 50000000000) : ℝ) ≤ Real.exp (2 * (467 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (467 / 12800)) (53784846043 / 50000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2339 / 64000) : ℝ)) ≤ (1075831391381 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2339 / 64000)) (1075831391381 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1884453121 / 1000000000) : ℝ) ≤ Real.exp (3 * (84485021 / 25000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (84485021 / 25000000) / 16) (1884453121 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3379824369 / 1000000000) : ℝ) / 16) ≤ (75384111 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3379824369 / 1000000000) / 16) (75384111 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((467 / 12800) : ℝ) (2339 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (84485021 / 25000000) (3379824369 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (467 / 12800) (2339 / 64000) (53784846043 / 50000000000) (1075831391381 / 1000000000000) (84485021 / 25000000) (3379824369 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (467 / 12800) (2339 / 64000) (84485021 / 25000000) (3379824369 / 1000000000) (9872401 / 250000000000) (9884953 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (84485021 / 25000000) (3379824369 / 1000000000) (1884453121 / 1000000000) (75384111 / 40000000) (9872401 / 250000000000) (9884953 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0689 :
    ∀ t ∈ Set.Icc ((2339 / 64000) : ℝ) (2343 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((53791569569 / 50000000000) : ℝ) ≤ Real.exp (2 * (2339 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2339 / 64000)) (53791569569 / 50000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2343 / 64000) : ℝ)) ≤ (107596587871 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2343 / 64000)) (107596587871 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((942301197 / 500000000) : ℝ) ≤ Real.exp (3 * (844955823 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (844955823 / 250000000) / 16) (942301197 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3380246873 / 1000000000) : ℝ) / 16) ≤ (1884752079 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3380246873 / 1000000000) / 16) (1884752079 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2339 / 64000) : ℝ) (2343 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (844955823 / 250000000) (3380246873 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2339 / 64000) (2343 / 64000) (53791569569 / 50000000000) (107596587871 / 100000000000) (844955823 / 250000000) (3380246873 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2339 / 64000) (2343 / 64000) (844955823 / 250000000) (3380246873 / 1000000000) (39439581 / 1000000000000) (9872433 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (844955823 / 250000000) (3380246873 / 1000000000) (942301197 / 500000000) (1884752079 / 1000000000) (39439581 / 1000000000000) (9872433 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0690 :
    ∀ t ∈ Set.Icc ((2343 / 64000) : ℝ) (2347 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1075965878709 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2343 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2343 / 64000)) (1075965878709 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2347 / 64000) : ℝ)) ≤ (1076100382851 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2347 / 64000)) (1076100382851 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1884751697 / 1000000000) : ℝ) ≤ Real.exp (3 * (845061449 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (845061449 / 250000000) / 16) (1884751697 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3380669431 / 1000000000) : ℝ) / 16) ≤ (1884901413 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3380669431 / 1000000000) / 16) (1884901413 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2343 / 64000) : ℝ) (2347 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (845061449 / 250000000) (3380669431 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2343 / 64000) (2347 / 64000) (1075965878709 / 1000000000000) (1076100382851 / 1000000000000) (845061449 / 250000000) (3380669431 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2343 / 64000) (2347 / 64000) (845061449 / 250000000) (3380669431 / 1000000000) (39389617 / 1000000000000) (3943971 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (845061449 / 250000000) (3380669431 / 1000000000) (1884751697 / 1000000000) (1884901413 / 1000000000) (39389617 / 1000000000000) (3943971 / 100000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0691 :
    ∀ t ∈ Set.Icc ((2347 / 64000) : ℝ) (2351 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((21522007657 / 20000000000) : ℝ) ≤ Real.exp (2 * (2347 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2347 / 64000)) (21522007657 / 20000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2351 / 64000) : ℝ)) ≤ (538117451903 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2351 / 64000)) (538117451903 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1884901031 / 1000000000) : ℝ) ≤ Real.exp (3 * (3380668353 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3380668353 / 1000000000) / 16) (1884901031 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3381092041 / 1000000000) : ℝ) / 16) ≤ (1885050777 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3381092041 / 1000000000) / 16) (1885050777 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2347 / 64000) : ℝ) (2351 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3380668353 / 1000000000) (3381092041 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2347 / 64000) (2351 / 64000) (21522007657 / 20000000000) (538117451903 / 500000000000) (3380668353 / 1000000000) (3381092041 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2347 / 64000) (2351 / 64000) (3380668353 / 1000000000) (3381092041 / 1000000000) (39339709 / 1000000000000) (7877949 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3380668353 / 1000000000) (3381092041 / 1000000000) (1884901031 / 1000000000) (1885050777 / 1000000000) (39339709 / 1000000000000) (7877949 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0692 :
    ∀ t ∈ Set.Icc ((2351 / 64000) : ℝ) (471 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((215246980761 / 200000000000) : ℝ) ≤ Real.exp (2 * (2351 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2351 / 64000)) (215246980761 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((471 / 12800) : ℝ)) ≤ (538184720789 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (471 / 12800)) (538184720789 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((377010079 / 200000000) : ℝ) ≤ Real.exp (3 * (3381090963 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3381090963 / 1000000000) / 16) (377010079 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((211344669 / 62500000) : ℝ) / 16) ≤ (471300043 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (211344669 / 62500000) / 16) (471300043 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2351 / 64000) : ℝ) (471 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3381090963 / 1000000000) (211344669 / 62500000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2351 / 64000) (471 / 12800) (215246980761 / 200000000000) (538184720789 / 500000000000) (3381090963 / 1000000000) (211344669 / 62500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2351 / 64000) (471 / 12800) (3381090963 / 1000000000) (211344669 / 62500000) (19644929 / 500000000000) (19669919 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3381090963 / 1000000000) (211344669 / 62500000) (377010079 / 200000000) (471300043 / 250000000) (19644929 / 500000000000) (19669919 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0693 :
    ∀ t ∈ Set.Icc ((471 / 12800) : ℝ) (2359 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1076369441577 / 1000000000000) : ℝ) ≤ Real.exp (2 * (471 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (471 / 12800)) (1076369441577 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2359 / 64000) : ℝ)) ≤ (1076503996167 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2359 / 64000)) (1076503996167 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((188519979 / 100000000) : ℝ) ≤ Real.exp (3 * (1690756813 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1690756813 / 500000000) / 16) (188519979 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3381937419 / 1000000000) : ℝ) / 16) ≤ (1885349597 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3381937419 / 1000000000) / 16) (1885349597 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((471 / 12800) : ℝ) (2359 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1690756813 / 500000000) (3381937419 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (471 / 12800) (2359 / 64000) (1076369441577 / 1000000000000) (1076503996167 / 1000000000000) (1690756813 / 500000000) (3381937419 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (471 / 12800) (2359 / 64000) (1690756813 / 500000000) (3381937419 / 1000000000) (7848013 / 200000000000) (39289987 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1690756813 / 500000000) (3381937419 / 1000000000) (188519979 / 100000000) (1885349597 / 1000000000) (7848013 / 200000000000) (39289987 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0694 :
    ∀ t ∈ Set.Icc ((2359 / 64000) : ℝ) (2363 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((538251998083 / 500000000000) : ℝ) ≤ Real.exp (2 * (2359 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2359 / 64000)) (538251998083 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2363 / 64000) : ℝ)) ≤ (1076638567577 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2363 / 64000)) (1076638567577 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((377069843 / 200000000) : ℝ) ≤ Real.exp (3 * (1690968171 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1690968171 / 500000000) / 16) (377069843 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((845590047 / 250000000) : ℝ) / 16) ≤ (1885499053 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (845590047 / 250000000) / 16) (1885499053 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2359 / 64000) : ℝ) (2363 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1690968171 / 500000000) (845590047 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2359 / 64000) (2363 / 64000) (538251998083 / 500000000000) (1076638567577 / 1000000000000) (1690968171 / 500000000) (845590047 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2359 / 64000) (2363 / 64000) (1690968171 / 500000000) (845590047 / 250000000) (4898791 / 125000000000) (39240193 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1690968171 / 500000000) (845590047 / 250000000) (377069843 / 200000000) (1885499053 / 1000000000) (4898791 / 125000000000) (39240193 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0695 :
    ∀ t ∈ Set.Icc ((2363 / 64000) : ℝ) (2367 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((134579820947 / 125000000000) : ℝ) ≤ Real.exp (2 * (2363 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2363 / 64000)) (134579820947 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2367 / 64000) : ℝ)) ≤ (107677315581 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2367 / 64000)) (107677315581 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1885498671 / 1000000000) : ℝ) ≤ Real.exp (3 * (338235911 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (338235911 / 100000000) / 16) (1885498671 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3382783009 / 1000000000) : ℝ) / 16) ≤ (1885648539 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3382783009 / 1000000000) / 16) (1885648539 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2363 / 64000) : ℝ) (2367 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (338235911 / 100000000) (3382783009 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2363 / 64000) (2367 / 64000) (134579820947 / 125000000000) (107677315581 / 100000000000) (338235911 / 100000000) (3382783009 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2363 / 64000) (2367 / 64000) (338235911 / 100000000) (3382783009 / 1000000000) (4892581 / 125000000000) (4898807 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (338235911 / 100000000) (3382783009 / 1000000000) (1885498671 / 1000000000) (1885648539 / 1000000000) (4892581 / 125000000000) (4898807 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0696 :
    ∀ t ∈ Set.Icc ((2367 / 64000) : ℝ) (2371 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1076773155809 / 1000000000000) : ℝ) ≤ Real.exp (2 * (2367 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2367 / 64000)) (1076773155809 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2371 / 64000) : ℝ)) ≤ (1076907760867 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2371 / 64000)) (1076907760867 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((942824079 / 500000000) : ℝ) ≤ Real.exp (3 * (845695483 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (845695483 / 250000000) / 16) (942824079 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((845801471 / 250000000) : ℝ) / 16) ≤ (1885798057 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (845801471 / 250000000) / 16) (1885798057 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2367 / 64000) : ℝ) (2371 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (845695483 / 250000000) (845801471 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2367 / 64000) (2371 / 64000) (1076773155809 / 1000000000000) (1076907760867 / 1000000000000) (845695483 / 250000000) (845801471 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2367 / 64000) (2371 / 64000) (845695483 / 250000000) (845801471 / 250000000) (2443189 / 62500000000) (4892597 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (845695483 / 250000000) (845801471 / 250000000) (942824079 / 500000000) (1885798057 / 1000000000) (2443189 / 62500000000) (4892597 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0697 :
    ∀ t ∈ Set.Icc ((2371 / 64000) : ℝ) (19 / 512), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((538453880433 / 500000000000) : ℝ) ≤ Real.exp (2 * (2371 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2371 / 64000)) (538453880433 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((19 / 512) : ℝ)) ≤ (1077042382751 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (19 / 512)) (1077042382751 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((942898837 / 500000000) : ℝ) ≤ Real.exp (3 * (1691602403 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1691602403 / 500000000) / 16) (942898837 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3383628811 / 1000000000) : ℝ) / 16) ≤ (471486901 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3383628811 / 1000000000) / 16) (471486901 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2371 / 64000) : ℝ) (19 / 512),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1691602403 / 500000000) (3383628811 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2371 / 64000) (19 / 512) (538453880433 / 500000000000) (1077042382751 / 1000000000000) (1691602403 / 500000000) (3383628811 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2371 / 64000) (19 / 512) (1691602403 / 500000000) (3383628811 / 1000000000) (19520729 / 500000000000) (2443197 / 62500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1691602403 / 500000000) (3383628811 / 1000000000) (942898837 / 500000000) (471486901 / 250000000) (19520729 / 500000000000) (2443197 / 62500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0698 :
    ∀ t ∈ Set.Icc ((19 / 512) : ℝ) (2379 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((4308169531 / 4000000000) : ℝ) ≤ Real.exp (2 * (19 / 512)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (19 / 512)) (4308169531 / 4000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2379 / 64000) : ℝ)) ≤ (1077177021463 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2379 / 64000)) (1077177021463 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((942973611 / 500000000) : ℝ) ≤ Real.exp (3 * (3383627733 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3383627733 / 1000000000) / 16) (942973611 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3384051791 / 1000000000) : ℝ) / 16) ≤ (943048591 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3384051791 / 1000000000) / 16) (943048591 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((19 / 512) : ℝ) (2379 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3383627733 / 1000000000) (3384051791 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (19 / 512) (2379 / 64000) (4308169531 / 4000000000) (1077177021463 / 1000000000000) (3383627733 / 1000000000) (3384051791 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (19 / 512) (2379 / 64000) (3383627733 / 1000000000) (3384051791 / 1000000000) (9747987 / 250000000000) (19520793 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3383627733 / 1000000000) (3384051791 / 1000000000) (942973611 / 500000000) (943048591 / 500000000) (9747987 / 250000000000) (19520793 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0699 :
    ∀ t ∈ Set.Icc ((2379 / 64000) : ℝ) (2383 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((538588510731 / 500000000000) : ℝ) ≤ Real.exp (2 * (2379 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (2379 / 64000)) (538588510731 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((2383 / 64000) : ℝ)) ≤ (1077311677007 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (2383 / 64000)) (1077311677007 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((2357621 / 1250000) : ℝ) ≤ Real.exp (3 * (3384050713 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3384050713 / 1000000000) / 16) (2357621 / 1250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((423059353 / 125000000) : ℝ) / 16) ≤ (1886246791 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (423059353 / 125000000) / 16) (1886246791 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((2379 / 64000) : ℝ) (2383 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3384050713 / 1000000000) (423059353 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (2379 / 64000) (2383 / 64000) (538588510731 / 500000000000) (1077311677007 / 1000000000000) (3384050713 / 1000000000) (423059353 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (2379 / 64000) (2383 / 64000) (3384050713 / 1000000000) (423059353 / 125000000) (7788499 / 200000000000) (9748019 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3384050713 / 1000000000) (423059353 / 125000000) (2357621 / 1250000) (1886246791 / 1000000000) (7788499 / 200000000000) (9748019 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch034 :
    ∀ t ∈ Set.Icc ((2303 / 64000) : ℝ) (2383 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0680
      hpThetaDensityTwoTermCompact_cell0681)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0682
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0683
      hpThetaDensityTwoTermCompact_cell0684)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0685
      hpThetaDensityTwoTermCompact_cell0686)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0687
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0688
      hpThetaDensityTwoTermCompact_cell0689))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0690
      hpThetaDensityTwoTermCompact_cell0691)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0692
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0693
      hpThetaDensityTwoTermCompact_cell0694)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0695
      hpThetaDensityTwoTermCompact_cell0696)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0697
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0698
      hpThetaDensityTwoTermCompact_cell0699)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch034
end HodgeProofHP
