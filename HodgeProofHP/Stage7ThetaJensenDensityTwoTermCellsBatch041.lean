/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0820 :
    ∀ t ∈ Set.Icc ((3019 / 64000) : ℝ) (3027 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((549468720371 / 500000000000) : ℝ) ≤ Real.exp (2 * (3019 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3019 / 64000)) (549468720371 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3027 / 64000) : ℝ)) ≤ (137401526181 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3027 / 64000)) (137401526181 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1910428287 / 1000000000) : ℝ) ≤ Real.exp (3 * (215775817 / 62500000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (215775817 / 62500000) / 16) (1910428287 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3453277383 / 1000000000) : ℝ) / 16) ≤ (1910737913 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3453277383 / 1000000000) / 16) (1910737913 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3019 / 64000) : ℝ) (3027 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (215775817 / 62500000) (3453277383 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3019 / 64000) (3027 / 64000) (549468720371 / 500000000000) (137401526181 / 125000000000) (215775817 / 62500000) (3453277383 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3019 / 64000) (3027 / 64000) (215775817 / 62500000) (3453277383 / 1000000000) (31679773 / 1000000000000) (3970253 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (215775817 / 62500000) (3453277383 / 1000000000) (1910428287 / 1000000000) (1910737913 / 1000000000) (31679773 / 1000000000000) (3970253 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0821 :
    ∀ t ∈ Set.Icc ((3027 / 64000) : ℝ) (607 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1099212209447 / 1000000000000) : ℝ) ≤ Real.exp (2 * (3027 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3027 / 64000)) (1099212209447 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((607 / 12800) : ℝ)) ≤ (1099487046853 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (607 / 12800)) (1099487046853 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((955368759 / 500000000) : ℝ) ≤ Real.exp (3 * (3453276283 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3453276283 / 1000000000) / 16) (955368759 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((345414081 / 100000000) : ℝ) / 16) ≤ (1911047273 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (345414081 / 100000000) / 16) (1911047273 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3027 / 64000) : ℝ) (607 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3453276283 / 1000000000) (345414081 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3027 / 64000) (607 / 12800) (1099212209447 / 1000000000000) (1099487046853 / 1000000000000) (3453276283 / 1000000000) (345414081 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3027 / 64000) (607 / 12800) (3453276283 / 1000000000) (345414081 / 100000000) (31597819 / 1000000000000) (31679879 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3453276283 / 1000000000) (345414081 / 100000000) (955368759 / 500000000) (1911047273 / 1000000000) (31597819 / 1000000000000) (31679879 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0822 :
    ∀ t ∈ Set.Icc ((607 / 12800) : ℝ) (3043 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((274871761713 / 250000000000) : ℝ) ≤ Real.exp (2 * (607 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (607 / 12800)) (274871761713 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3043 / 64000) : ℝ)) ≤ (1099761952977 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3043 / 64000)) (1099761952977 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((955523439 / 500000000) : ℝ) ≤ Real.exp (3 * (345413971 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (345413971 / 100000000) / 16) (955523439 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1727502227 / 500000000) : ℝ) / 16) ≤ (47783919 / 25000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1727502227 / 500000000) / 16) (47783919 / 25000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((607 / 12800) : ℝ) (3043 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (345413971 / 100000000) (1727502227 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (607 / 12800) (3043 / 64000) (274871761713 / 250000000000) (1099761952977 / 1000000000000) (345413971 / 100000000) (1727502227 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (607 / 12800) (3043 / 64000) (345413971 / 100000000) (1727502227 / 500000000) (31516057 / 1000000000000) (1263917 / 40000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (345413971 / 100000000) (1727502227 / 500000000) (955523439 / 500000000) (47783919 / 25000000) (31516057 / 1000000000000) (1263917 / 40000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0823 :
    ∀ t ∈ Set.Icc ((3043 / 64000) : ℝ) (3051 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((68735122061 / 62500000000) : ℝ) ≤ Real.exp (2 * (3043 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3043 / 64000)) (68735122061 / 62500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3051 / 64000) : ℝ)) ≤ (275009231959 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3051 / 64000)) (275009231959 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((477839091 / 250000000) : ℝ) ≤ Real.exp (3 * (3455003353 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3455003353 / 1000000000) / 16) (477839091 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3455868313 / 1000000000) : ℝ) / 16) ≤ (955833187 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3455868313 / 1000000000) / 16) (955833187 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3043 / 64000) : ℝ) (3051 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3455003353 / 1000000000) (3455868313 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3043 / 64000) (3051 / 64000) (68735122061 / 62500000000) (275009231959 / 250000000000) (3455003353 / 1000000000) (3455868313 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3043 / 64000) (3051 / 64000) (3455003353 / 1000000000) (3455868313 / 1000000000) (31434487 / 1000000000000) (31516163 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3455003353 / 1000000000) (3455868313 / 1000000000) (477839091 / 250000000) (955833187 / 500000000) (31434487 / 1000000000000) (31516163 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0824 :
    ∀ t ∈ Set.Icc ((3051 / 64000) : ℝ) (3059 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((220007385567 / 200000000000) : ℝ) ≤ Real.exp (2 * (3051 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3051 / 64000)) (220007385567 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3059 / 64000) : ℝ)) ≤ (1100311971447 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3059 / 64000)) (1100311971447 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1911665979 / 1000000000) : ℝ) ≤ Real.exp (3 * (863966803 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (863966803 / 250000000) / 16) (1911665979 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((864183097 / 250000000) : ℝ) / 16) ≤ (477994029 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (864183097 / 250000000) / 16) (477994029 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3051 / 64000) : ℝ) (3059 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (863966803 / 250000000) (864183097 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3051 / 64000) (3059 / 64000) (220007385567 / 200000000000) (1100311971447 / 1000000000000) (863966803 / 250000000) (864183097 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3051 / 64000) (3059 / 64000) (863966803 / 250000000) (864183097 / 250000000) (31353107 / 1000000000000) (982331 / 31250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (863966803 / 250000000) (864183097 / 250000000) (1911665979 / 1000000000) (477994029 / 250000000) (31353107 / 1000000000000) (982331 / 31250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0825 :
    ∀ t ∈ Set.Icc ((3059 / 64000) : ℝ) (3067 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((550155985723 / 500000000000) : ℝ) ≤ Real.exp (2 * (3059 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3059 / 64000)) (550155985723 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3067 / 64000) : ℝ)) ≤ (1100587083827 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3067 / 64000)) (1100587083827 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((47799393 / 25000000) : ℝ) ≤ Real.exp (3 * (1728365643 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1728365643 / 500000000) / 16) (47799393 / 25000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3457596679 / 1000000000) : ℝ) / 16) ≤ (956142993 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3457596679 / 1000000000) / 16) (956142993 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3059 / 64000) : ℝ) (3067 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1728365643 / 500000000) (3457596679 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3059 / 64000) (3067 / 64000) (550155985723 / 500000000000) (1100587083827 / 1000000000000) (1728365643 / 500000000) (3457596679 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3059 / 64000) (3067 / 64000) (1728365643 / 500000000) (3457596679 / 1000000000) (15635959 / 500000000000) (7838303 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1728365643 / 500000000) (3457596679 / 1000000000) (47799393 / 25000000) (956142993 / 500000000) (15635959 / 500000000000) (7838303 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0826 :
    ∀ t ∈ Set.Icc ((3067 / 64000) : ℝ) (123 / 2560), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((550293541913 / 500000000000) : ℝ) ≤ Real.exp (2 * (3067 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3067 / 64000)) (550293541913 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((123 / 2560) : ℝ)) ≤ (550431132497 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (123 / 2560)) (550431132497 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((191228559 / 100000000) : ℝ) ≤ Real.exp (3 * (3457595577 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3457595577 / 1000000000) / 16) (191228559 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1729230593 / 500000000) : ℝ) / 16) ≤ (1912595983 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1729230593 / 500000000) / 16) (1912595983 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3067 / 64000) : ℝ) (123 / 2560),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3457595577 / 1000000000) (1729230593 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3067 / 64000) (123 / 2560) (550293541913 / 500000000000) (550431132497 / 500000000000) (3457595577 / 1000000000) (1729230593 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3067 / 64000) (123 / 2560) (3457595577 / 1000000000) (1729230593 / 500000000) (31190919 / 1000000000000) (15636011 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3457595577 / 1000000000) (1729230593 / 500000000) (191228559 / 100000000) (1912595983 / 1000000000) (31190919 / 1000000000000) (15636011 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0827 :
    ∀ t ∈ Set.Icc ((123 / 2560) : ℝ) (3083 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1100862264993 / 1000000000000) : ℝ) ≤ Real.exp (2 * (123 / 2560)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (123 / 2560)) (1100862264993 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3083 / 64000) : ℝ)) ≤ (220227502993 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3083 / 64000)) (220227502993 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1912595587 / 1000000000) : ℝ) ≤ Real.exp (3 * (864615021 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (864615021 / 250000000) / 16) (1912595587 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((345932591 / 100000000) : ℝ) / 16) ≤ (478226527 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (345932591 / 100000000) / 16) (478226527 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((123 / 2560) : ℝ) (3083 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (864615021 / 250000000) (345932591 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (123 / 2560) (3083 / 64000) (1100862264993 / 1000000000000) (220227502993 / 200000000000) (864615021 / 250000000) (345932591 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (123 / 2560) (3083 / 64000) (864615021 / 250000000) (345932591 / 100000000) (31110109 / 1000000000000) (31191023 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (864615021 / 250000000) (345932591 / 100000000) (1912595587 / 1000000000) (478226527 / 250000000) (31110109 / 1000000000000) (31191023 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0828 :
    ∀ t ∈ Set.Icc ((3083 / 64000) : ℝ) (3091 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((275284378741 / 250000000000) : ℝ) ≤ Real.exp (2 * (3083 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3083 / 64000)) (275284378741 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3091 / 64000) : ℝ)) ≤ (1101412833757 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3091 / 64000)) (1101412833757 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((119556607 / 62500000) : ℝ) ≤ Real.exp (3 * (3459324807 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3459324807 / 1000000000) / 16) (119556607 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3460190849 / 1000000000) : ℝ) / 16) ≤ (1913216361 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3460190849 / 1000000000) / 16) (1913216361 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3083 / 64000) : ℝ) (3091 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3459324807 / 1000000000) (3460190849 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3083 / 64000) (3091 / 64000) (275284378741 / 250000000000) (1101412833757 / 1000000000000) (3459324807 / 1000000000) (3460190849 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3083 / 64000) (3091 / 64000) (3459324807 / 1000000000) (3460190849 / 1000000000) (1939343 / 62500000000) (31110213 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3459324807 / 1000000000) (3460190849 / 1000000000) (119556607 / 62500000) (1913216361 / 1000000000) (1939343 / 62500000000) (31110213 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0829 :
    ∀ t ∈ Set.Icc ((3091 / 64000) : ℝ) (3099 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((275353208439 / 250000000000) : ℝ) ≤ Real.exp (2 * (3091 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3091 / 64000)) (275353208439 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3099 / 64000) : ℝ)) ≤ (275422055347 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3099 / 64000)) (275422055347 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((382643193 / 200000000) : ℝ) ≤ Real.exp (3 * (3460189747 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3460189747 / 1000000000) / 16) (382643193 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((692211201 / 200000000) : ℝ) / 16) ≤ (956763371 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (692211201 / 200000000) / 16) (956763371 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3091 / 64000) : ℝ) (3099 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3460189747 / 1000000000) (692211201 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3091 / 64000) (3099 / 64000) (275353208439 / 250000000000) (275422055347 / 250000000000) (3460189747 / 1000000000) (692211201 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3091 / 64000) (3099 / 64000) (3460189747 / 1000000000) (692211201 / 200000000) (30949057 / 1000000000000) (3878699 / 125000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3460189747 / 1000000000) (692211201 / 200000000) (382643193 / 200000000) (956763371 / 500000000) (30949057 / 1000000000000) (3878699 / 125000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0830 :
    ∀ t ∈ Set.Icc ((3099 / 64000) : ℝ) (3107 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1101688221387 / 1000000000000) : ℝ) ≤ Real.exp (2 * (3099 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3099 / 64000)) (1101688221387 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3107 / 64000) : ℝ)) ≤ (550981838937 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3107 / 64000)) (550981838937 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((382705269 / 200000000) : ℝ) ≤ Real.exp (3 * (1730527451 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1730527451 / 500000000) / 16) (382705269 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3461921377 / 1000000000) : ℝ) / 16) ≤ (1913837251 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3461921377 / 1000000000) / 16) (1913837251 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3099 / 64000) : ℝ) (3107 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1730527451 / 500000000) (3461921377 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3099 / 64000) (3107 / 64000) (1101688221387 / 1000000000000) (550981838937 / 500000000000) (1730527451 / 500000000) (3461921377 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3099 / 64000) (3107 / 64000) (1730527451 / 500000000) (3461921377 / 1000000000) (15434407 / 500000000000) (773729 / 25000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1730527451 / 500000000) (3461921377 / 1000000000) (382705269 / 200000000) (1913837251 / 1000000000) (15434407 / 500000000000) (773729 / 25000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0831 :
    ∀ t ∈ Set.Icc ((3107 / 64000) : ℝ) (623 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1101963677873 / 1000000000000) : ℝ) ≤ Real.exp (2 * (3107 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3107 / 64000)) (1101963677873 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((623 / 12800) : ℝ)) ≤ (1102239203233 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (623 / 12800)) (1102239203233 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((956918427 / 500000000) : ℝ) ≤ Real.exp (3 * (1730960137 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1730960137 / 500000000) / 16) (956918427 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1731393483 / 500000000) : ℝ) / 16) ≤ (119634243 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1731393483 / 500000000) / 16) (119634243 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3107 / 64000) : ℝ) (623 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1730960137 / 500000000) (1731393483 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3107 / 64000) (623 / 12800) (1101963677873 / 1000000000000) (1102239203233 / 1000000000000) (1730960137 / 500000000) (1731393483 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3107 / 64000) (623 / 12800) (1730960137 / 500000000) (1731393483 / 500000000) (15394379 / 500000000000) (30868917 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1730960137 / 500000000) (1731393483 / 500000000) (956918427 / 500000000) (119634243 / 62500000) (15394379 / 500000000000) (30868917 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0832 :
    ∀ t ∈ Set.Icc ((623 / 12800) : ℝ) (3123 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((34444975101 / 31250000000) : ℝ) ≤ Real.exp (2 * (623 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (623 / 12800)) (34444975101 / 31250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3123 / 64000) : ℝ)) ≤ (1102514797481 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3123 / 64000)) (1102514797481 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1914147491 / 1000000000) : ℝ) ≤ Real.exp (3 * (1731392931 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1731392931 / 500000000) / 16) (1914147491 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3463652771 / 1000000000) : ℝ) / 16) ≤ (1914458653 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3463652771 / 1000000000) / 16) (1914458653 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((623 / 12800) : ℝ) (3123 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1731392931 / 500000000) (3463652771 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (623 / 12800) (3123 / 64000) (34444975101 / 31250000000) (1102514797481 / 1000000000000) (1731392931 / 500000000) (3463652771 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (623 / 12800) (3123 / 64000) (1731392931 / 500000000) (3463652771 / 1000000000) (30708891 / 1000000000000) (15394431 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1731392931 / 500000000) (3463652771 / 1000000000) (1914147491 / 1000000000) (1914458653 / 1000000000) (30708891 / 1000000000000) (15394431 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0833 :
    ∀ t ∈ Set.Icc ((3123 / 64000) : ℝ) (3131 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((27562869937 / 25000000000) : ℝ) ≤ Real.exp (2 * (3123 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3123 / 64000)) (27562869937 / 25000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3131 / 64000) : ℝ)) ≤ (1102790460637 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3131 / 64000)) (1102790460637 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((382891651 / 200000000) : ℝ) ≤ Real.exp (3 * (3463651667 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3463651667 / 1000000000) / 16) (382891651 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((433064849 / 125000000) : ℝ) / 16) ≤ (957384773 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (433064849 / 125000000) / 16) (957384773 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3123 / 64000) : ℝ) (3131 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3463651667 / 1000000000) (433064849 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3123 / 64000) (3131 / 64000) (27562869937 / 25000000000) (1102790460637 / 1000000000000) (3463651667 / 1000000000) (433064849 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3123 / 64000) (3131 / 64000) (3463651667 / 1000000000) (433064849 / 125000000) (30629211 / 1000000000000) (15354497 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3463651667 / 1000000000) (433064849 / 125000000) (382891651 / 200000000) (957384773 / 500000000) (30629211 / 1000000000000) (15354497 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0834 :
    ∀ t ∈ Set.Icc ((3131 / 64000) : ℝ) (3139 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((275697615159 / 250000000000) : ℝ) ≤ Real.exp (2 * (3131 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3131 / 64000)) (275697615159 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3139 / 64000) : ℝ)) ≤ (1103066192717 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3139 / 64000)) (1103066192717 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((478692287 / 250000000) : ℝ) ≤ Real.exp (3 * (433064711 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (433064711 / 125000000) / 16) (478692287 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((346538503 / 100000000) : ℝ) / 16) ≤ (1915080567 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (346538503 / 100000000) / 16) (1915080567 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3131 / 64000) : ℝ) (3139 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (433064711 / 125000000) (346538503 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3131 / 64000) (3139 / 64000) (275697615159 / 250000000000) (1103066192717 / 1000000000000) (433064711 / 125000000) (346538503 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3131 / 64000) (3139 / 64000) (433064711 / 125000000) (346538503 / 100000000) (15274859 / 500000000000) (15314657 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (433064711 / 125000000) (346538503 / 100000000) (478692287 / 250000000) (1915080567 / 1000000000) (15274859 / 500000000000) (15314657 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0835 :
    ∀ t ∈ Set.Icc ((3139 / 64000) : ℝ) (3147 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((275766548179 / 250000000000) : ℝ) ≤ Real.exp (2 * (3139 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3139 / 64000)) (275766548179 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3147 / 64000) : ℝ)) ≤ (1103341993739 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3147 / 64000)) (1103341993739 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((191508017 / 100000000) : ℝ) ≤ Real.exp (3 * (1732691963 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1732691963 / 500000000) / 16) (191508017 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((693250297 / 200000000) : ℝ) / 16) ≤ (1915391717 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (693250297 / 200000000) / 16) (1915391717 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3139 / 64000) : ℝ) (3147 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1732691963 / 500000000) (693250297 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3139 / 64000) (3147 / 64000) (275766548179 / 250000000000) (1103341993739 / 1000000000000) (1732691963 / 500000000) (693250297 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3139 / 64000) (3147 / 64000) (1732691963 / 500000000) (693250297 / 200000000) (30470411 / 1000000000000) (1527491 / 50000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1732691963 / 500000000) (693250297 / 200000000) (191508017 / 100000000) (1915391717 / 1000000000) (30470411 / 1000000000000) (1527491 / 50000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0836 :
    ∀ t ∈ Set.Icc ((3147 / 64000) : ℝ) (631 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((551670996869 / 500000000000) : ℝ) ≤ Real.exp (2 * (3147 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3147 / 64000)) (551670996869 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((631 / 12800) : ℝ)) ≤ (27590446593 / 25000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (631 / 12800)) (27590446593 / 25000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1915391319 / 1000000000) : ℝ) ≤ Real.exp (3 * (173312519 / 50000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (173312519 / 50000000) / 16) (1915391319 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((866779539 / 250000000) : ℝ) / 16) ≤ (383140599 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (866779539 / 250000000) / 16) (383140599 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3147 / 64000) : ℝ) (631 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (173312519 / 50000000) (866779539 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3147 / 64000) (631 / 12800) (551670996869 / 500000000000) (27590446593 / 25000000000) (173312519 / 50000000) (866779539 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3147 / 64000) (631 / 12800) (173312519 / 50000000) (866779539 / 250000000) (3039129 / 100000000000) (30470513 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (173312519 / 50000000) (866779539 / 250000000) (1915391319 / 1000000000) (383140599 / 200000000) (3039129 / 100000000000) (30470513 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0837 :
    ∀ t ∈ Set.Icc ((631 / 12800) : ℝ) (3163 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1103617863719 / 1000000000000) : ℝ) ≤ Real.exp (2 * (631 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (631 / 12800)) (1103617863719 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3163 / 64000) : ℝ)) ≤ (1103893802677 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3163 / 64000)) (1103893802677 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1915702597 / 1000000000) : ℝ) ≤ Real.exp (3 * (3467117051 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3467117051 / 1000000000) / 16) (1915702597 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((866996261 / 250000000) : ℝ) / 16) ≤ (958007201 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (866996261 / 250000000) / 16) (958007201 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((631 / 12800) : ℝ) (3163 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3467117051 / 1000000000) (866996261 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (631 / 12800) (3163 / 64000) (1103617863719 / 1000000000000) (1103893802677 / 1000000000000) (3467117051 / 1000000000) (866996261 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (631 / 12800) (3163 / 64000) (3467117051 / 1000000000) (866996261 / 250000000) (7578089 / 250000000000) (949731 / 31250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3467117051 / 1000000000) (866996261 / 250000000) (1915702597 / 1000000000) (958007201 / 500000000) (7578089 / 250000000000) (949731 / 31250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0838 :
    ∀ t ∈ Set.Icc ((3163 / 64000) : ℝ) (3171 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((275973450669 / 250000000000) : ℝ) ≤ Real.exp (2 * (3163 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3163 / 64000)) (275973450669 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3171 / 64000) : ℝ)) ≤ (1104169810627 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3171 / 64000)) (1104169810627 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((479003501 / 250000000) : ℝ) ≤ Real.exp (3 * (3467983939 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3467983939 / 1000000000) / 16) (479003501 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((867213037 / 250000000) : ℝ) / 16) ≤ (119770371 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (867213037 / 250000000) / 16) (119770371 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3163 / 64000) : ℝ) (3171 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3467983939 / 1000000000) (867213037 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3163 / 64000) (3171 / 64000) (275973450669 / 250000000000) (1104169810627 / 1000000000000) (3467983939 / 1000000000) (867213037 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3163 / 64000) (3171 / 64000) (3467983939 / 1000000000) (867213037 / 250000000) (15116803 / 500000000000) (30312457 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3467983939 / 1000000000) (867213037 / 250000000) (479003501 / 250000000) (119770371 / 62500000) (15116803 / 500000000000) (30312457 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0839 :
    ∀ t ∈ Set.Icc ((3171 / 64000) : ℝ) (3179 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((552084905313 / 500000000000) : ℝ) ≤ Real.exp (2 * (3171 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3171 / 64000)) (552084905313 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3179 / 64000) : ℝ)) ≤ (276111471897 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3179 / 64000)) (276111471897 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((958162769 / 500000000) : ℝ) ≤ Real.exp (3 * (3468851043 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3468851043 / 1000000000) / 16) (958162769 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((346971947 / 100000000) : ℝ) / 16) ≤ (2395797 / 1250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (346971947 / 100000000) / 16) (2395797 / 1250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3171 / 64000) : ℝ) (3179 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3468851043 / 1000000000) (346971947 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3171 / 64000) (3179 / 64000) (552084905313 / 500000000000) (276111471897 / 250000000000) (3468851043 / 1000000000) (346971947 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3171 / 64000) (3179 / 64000) (3468851043 / 1000000000) (346971947 / 100000000) (15077521 / 500000000000) (7558427 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3468851043 / 1000000000) (346971947 / 100000000) (958162769 / 500000000) (2395797 / 1250000) (15077521 / 500000000000) (7558427 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch041 :
    ∀ t ∈ Set.Icc ((3019 / 64000) : ℝ) (3179 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0820
      hpThetaDensityTwoTermCompact_cell0821)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0822
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0823
      hpThetaDensityTwoTermCompact_cell0824)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0825
      hpThetaDensityTwoTermCompact_cell0826)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0827
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0828
      hpThetaDensityTwoTermCompact_cell0829))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0830
      hpThetaDensityTwoTermCompact_cell0831)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0832
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0833
      hpThetaDensityTwoTermCompact_cell0834)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0835
      hpThetaDensityTwoTermCompact_cell0836)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0837
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0838
      hpThetaDensityTwoTermCompact_cell0839)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch041
end HodgeProofHP
