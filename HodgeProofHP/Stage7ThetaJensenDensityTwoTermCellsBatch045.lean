/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0900 :
    ∀ t ∈ Set.Icc ((3811 / 64000) : ℝ) (3827 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((563237760209 / 500000000000) : ℝ) ≤ Real.exp (2 * (3811 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3811 / 64000)) (563237760209 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3827 / 64000) : ℝ)) ≤ (281759724753 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3827 / 64000)) (281759724753 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1941670559 / 1000000000) : ℝ) ≤ Real.exp (3 * (3538926483 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3538926483 / 1000000000) / 16) (1941670559 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((885174379 / 250000000) : ℝ) / 16) ≤ (388463087 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (885174379 / 250000000) / 16) (388463087 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3811 / 64000) : ℝ) (3827 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3538926483 / 1000000000) (885174379 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3811 / 64000) (3827 / 64000) (563237760209 / 500000000000) (281759724753 / 250000000000) (3538926483 / 1000000000) (885174379 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3811 / 64000) (3827 / 64000) (3538926483 / 1000000000) (885174379 / 250000000) (24371587 / 1000000000000) (24501421 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3538926483 / 1000000000) (885174379 / 250000000) (1941670559 / 1000000000) (388463087 / 200000000) (24371587 / 1000000000000) (24501421 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0901 :
    ∀ t ∈ Set.Icc ((3827 / 64000) : ℝ) (3843 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1127038899011 / 1000000000000) : ℝ) ≤ Real.exp (2 * (3827 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3827 / 64000)) (1127038899011 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3843 / 64000) : ℝ)) ≤ (225520511873 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3843 / 64000)) (225520511873 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1942315023 / 1000000000) : ℝ) ≤ Real.exp (3 * (885174097 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (885174097 / 250000000) / 16) (1942315023 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((885617077 / 250000000) : ℝ) / 16) ≤ (485740109 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (885617077 / 250000000) / 16) (485740109 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3827 / 64000) : ℝ) (3843 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (885174097 / 250000000) (885617077 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3827 / 64000) (3843 / 64000) (1127038899011 / 1000000000000) (225520511873 / 200000000000) (885174097 / 250000000) (885617077 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3827 / 64000) (3843 / 64000) (885174097 / 250000000) (885617077 / 250000000) (24242459 / 1000000000000) (24371671 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (885174097 / 250000000) (885617077 / 250000000) (1942315023 / 1000000000) (485740109 / 250000000) (24242459 / 1000000000000) (24371671 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0902 :
    ∀ t ∈ Set.Icc ((3843 / 64000) : ℝ) (3859 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((281900639841 / 250000000000) : ℝ) ≤ Real.exp (2 * (3843 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3843 / 64000)) (281900639841 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3859 / 64000) : ℝ)) ≤ (564083250809 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3859 / 64000)) (564083250809 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((242870003 / 125000000) : ℝ) ≤ Real.exp (3 * (3542467179 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3542467179 / 1000000000) / 16) (242870003 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((708847997 / 200000000) : ℝ) / 16) ≤ (971802987 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (708847997 / 200000000) / 16) (971802987 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3843 / 64000) : ℝ) (3859 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3542467179 / 1000000000) (708847997 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3843 / 64000) (3859 / 64000) (281900639841 / 250000000000) (564083250809 / 500000000000) (3542467179 / 1000000000) (708847997 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3843 / 64000) (3859 / 64000) (3542467179 / 1000000000) (708847997 / 200000000) (753561 / 31250000000) (24242543 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3542467179 / 1000000000) (708847997 / 200000000) (242870003 / 125000000) (971802987 / 500000000) (753561 / 31250000000) (24242543 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0903 :
    ∀ t ∈ Set.Icc ((3859 / 64000) : ℝ) (31 / 512), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1128166501617 / 1000000000000) : ℝ) ≤ Real.exp (2 * (3859 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3859 / 64000)) (1128166501617 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((31 / 512) : ℝ)) ≤ (1128730725913 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (31 / 512)) (1128730725913 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((971802781 / 500000000) : ℝ) ≤ Real.exp (3 * (443029857 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (443029857 / 125000000) / 16) (971802781 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((886503137 / 250000000) : ℝ) / 16) ≤ (38885041 / 20000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (886503137 / 250000000) / 16) (38885041 / 20000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3859 / 64000) : ℝ) (31 / 512),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (443029857 / 125000000) (886503137 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3859 / 64000) (31 / 512) (1128166501617 / 1000000000000) (1128730725913 / 1000000000000) (443029857 / 125000000) (886503137 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3859 / 64000) (31 / 512) (443029857 / 125000000) (886503137 / 250000000) (23986061 / 1000000000000) (12057017 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (443029857 / 125000000) (886503137 / 250000000) (971802781 / 500000000) (38885041 / 20000000) (23986061 / 1000000000000) (12057017 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0904 :
    ∀ t ∈ Set.Icc ((31 / 512) : ℝ) (3891 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((141091340739 / 125000000000) : ℝ) ≤ Real.exp (2 * (31 / 512)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (31 / 512)) (141091340739 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3891 / 64000) : ℝ)) ≤ (1129295232391 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3891 / 64000)) (1129295232391 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1944251637 / 1000000000) : ℝ) ≤ Real.exp (3 * (1773005709 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1773005709 / 500000000) / 16) (1944251637 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1773892999 / 500000000) : ℝ) / 16) ≤ (243112333 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1773892999 / 500000000) / 16) (243112333 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((31 / 512) : ℝ) (3891 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1773005709 / 500000000) (1773892999 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (31 / 512) (3891 / 64000) (141091340739 / 125000000000) (1129295232391 / 1000000000000) (1773005709 / 500000000) (1773892999 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (31 / 512) (3891 / 64000) (1773005709 / 500000000) (1773892999 / 500000000) (11929393 / 500000000000) (749567 / 31250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1773005709 / 500000000) (1773892999 / 500000000) (1944251637 / 1000000000) (243112333 / 125000000) (11929393 / 500000000000) (749567 / 31250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0905 :
    ∀ t ∈ Set.Icc ((3891 / 64000) : ℝ) (3907 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((112929523239 / 100000000000) : ℝ) ≤ Real.exp (2 * (3891 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3891 / 64000)) (112929523239 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3907 / 64000) : ℝ)) ≤ (1129860021193 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3907 / 64000)) (1129860021193 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((7779593 / 4000000) : ℝ) ≤ Real.exp (3 * (3547784867 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3547784867 / 1000000000) / 16) (7779593 / 4000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1774780167 / 500000000) : ℝ) / 16) ≤ (243193227 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1774780167 / 500000000) / 16) (243193227 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3891 / 64000) : ℝ) (3907 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3547784867 / 1000000000) (1774780167 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3891 / 64000) (3907 / 64000) (112929523239 / 100000000000) (1129860021193 / 1000000000000) (3547784867 / 1000000000) (1774780167 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3891 / 64000) (3907 / 64000) (3547784867 / 1000000000) (1774780167 / 500000000) (23732123 / 1000000000000) (5964717 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3547784867 / 1000000000) (1774780167 / 500000000) (7779593 / 4000000) (243193227 / 125000000) (23732123 / 1000000000000) (5964717 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0906 :
    ∀ t ∈ Set.Icc ((3907 / 64000) : ℝ) (3923 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((141232502649 / 125000000000) : ℝ) ≤ Real.exp (2 * (3907 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3907 / 64000)) (141232502649 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3923 / 64000) : ℝ)) ≤ (1130425092459 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3923 / 64000)) (1130425092459 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((972772701 / 500000000) : ℝ) ≤ Real.exp (3 * (3549559203 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3549559203 / 1000000000) / 16) (972772701 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1775667779 / 500000000) : ℝ) / 16) ≤ (1946193507 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1775667779 / 500000000) / 16) (1946193507 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3907 / 64000) : ℝ) (3923 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3549559203 / 1000000000) (1775667779 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3907 / 64000) (3923 / 64000) (141232502649 / 125000000000) (1130425092459 / 1000000000000) (3549559203 / 1000000000) (1775667779 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3907 / 64000) (3923 / 64000) (3549559203 / 1000000000) (1775667779 / 500000000) (2360607 / 100000000000) (4746441 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3549559203 / 1000000000) (1775667779 / 500000000) (972772701 / 500000000) (1946193507 / 1000000000) (2360607 / 100000000000) (4746441 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0907 :
    ∀ t ∈ Set.Icc ((3923 / 64000) : ℝ) (3939 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((565212546229 / 500000000000) : ℝ) ≤ Real.exp (2 * (3923 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3923 / 64000)) (565212546229 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3939 / 64000) : ℝ)) ≤ (282747611583 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3939 / 64000)) (282747611583 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((973096547 / 500000000) : ℝ) ≤ Real.exp (3 * (3551334427 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3551334427 / 1000000000) / 16) (973096547 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((355311167 / 100000000) : ℝ) / 16) ≤ (1946841739 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (355311167 / 100000000) / 16) (1946841739 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3923 / 64000) : ℝ) (3939 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3551334427 / 1000000000) (355311167 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3923 / 64000) (3939 / 64000) (565212546229 / 500000000000) (282747611583 / 250000000000) (3551334427 / 1000000000) (355311167 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3923 / 64000) (3939 / 64000) (3551334427 / 1000000000) (355311167 / 100000000) (23480623 / 1000000000000) (23606151 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3551334427 / 1000000000) (355311167 / 100000000) (973096547 / 500000000) (1946841739 / 1000000000) (23480623 / 1000000000000) (23606151 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0908 :
    ∀ t ∈ Set.Icc ((3939 / 64000) : ℝ) (791 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1130990446331 / 1000000000000) : ℝ) ≤ Real.exp (2 * (3939 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3939 / 64000)) (1130990446331 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((791 / 12800) : ℝ)) ≤ (1131556082953 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (791 / 12800)) (1131556082953 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((486710331 / 250000000) : ℝ) ≤ Real.exp (3 * (1776555269 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1776555269 / 500000000) / 16) (486710331 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((355488867 / 100000000) : ℝ) / 16) ≤ (194749051 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (355488867 / 100000000) / 16) (194749051 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3939 / 64000) : ℝ) (791 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1776555269 / 500000000) (355488867 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3939 / 64000) (791 / 12800) (1130990446331 / 1000000000000) (1131556082953 / 1000000000000) (1776555269 / 500000000) (355488867 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3939 / 64000) (791 / 12800) (1776555269 / 500000000) (355488867 / 100000000) (23355781 / 1000000000000) (183443 / 7812500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1776555269 / 500000000) (355488867 / 100000000) (486710331 / 250000000) (194749051 / 100000000) (23355781 / 1000000000000) (183443 / 7812500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0909 :
    ∀ t ∈ Set.Icc ((791 / 12800) : ℝ) (3971 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((141444510369 / 125000000000) : ℝ) ≤ Real.exp (2 * (791 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (791 / 12800)) (141444510369 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3971 / 64000) : ℝ)) ≤ (566061001231 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3971 / 64000)) (566061001231 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((389498019 / 200000000) : ℝ) ≤ Real.exp (3 * (3554887537 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3554887537 / 1000000000) / 16) (389498019 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3556666559 / 1000000000) : ℝ) / 16) ≤ (974069911 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3556666559 / 1000000000) / 16) (974069911 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((791 / 12800) : ℝ) (3971 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3554887537 / 1000000000) (3556666559 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (791 / 12800) (3971 / 64000) (141444510369 / 125000000000) (566061001231 / 500000000000) (3554887537 / 1000000000) (3556666559 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (791 / 12800) (3971 / 64000) (3554887537 / 1000000000) (3556666559 / 1000000000) (1161577 / 50000000000) (23355861 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3554887537 / 1000000000) (3556666559 / 1000000000) (389498019 / 200000000) (974069911 / 500000000) (1161577 / 50000000000) (23355861 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0910 :
    ∀ t ∈ Set.Icc ((3971 / 64000) : ℝ) (3987 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1132122002461 / 1000000000000) : ℝ) ≤ Real.exp (2 * (3971 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3971 / 64000)) (1132122002461 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3987 / 64000) : ℝ)) ≤ (566344102501 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3987 / 64000)) (566344102501 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1948139407 / 1000000000) : ℝ) ≤ Real.exp (3 * (142266617 / 40000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (142266617 / 40000000) / 16) (1948139407 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3558445337 / 1000000000) : ℝ) / 16) ≤ (487197419 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3558445337 / 1000000000) / 16) (487197419 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3971 / 64000) : ℝ) (3987 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (142266617 / 40000000) (3558445337 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3971 / 64000) (3987 / 64000) (1132122002461 / 1000000000000) (566344102501 / 500000000000) (142266617 / 40000000) (3558445337 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3971 / 64000) (3987 / 64000) (142266617 / 40000000) (3558445337 / 1000000000) (23107899 / 1000000000000) (23231621 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (142266617 / 40000000) (3558445337 / 1000000000) (1948139407 / 1000000000) (487197419 / 250000000) (23107899 / 1000000000000) (23231621 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0911 :
    ∀ t ∈ Set.Icc ((3987 / 64000) : ℝ) (4003 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1132688205001 / 1000000000000) : ℝ) ≤ Real.exp (2 * (3987 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3987 / 64000)) (1132688205001 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4003 / 64000) : ℝ)) ≤ (226650938143 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4003 / 64000)) (226650938143 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1948789261 / 1000000000) : ℝ) ≤ Real.exp (3 * (3558444203 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3558444203 / 1000000000) / 16) (1948789261 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((890056251 / 250000000) : ℝ) / 16) ≤ (1949440071 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (890056251 / 250000000) / 16) (1949440071 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3987 / 64000) : ℝ) (4003 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3558444203 / 1000000000) (890056251 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3987 / 64000) (4003 / 64000) (1132688205001 / 1000000000000) (226650938143 / 200000000000) (3558444203 / 1000000000) (890056251 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3987 / 64000) (4003 / 64000) (3558444203 / 1000000000) (890056251 / 250000000) (4596971 / 200000000000) (23107979 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3558444203 / 1000000000) (890056251 / 250000000) (1948789261 / 1000000000) (1949440071 / 1000000000) (4596971 / 200000000000) (23107979 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0912 :
    ∀ t ∈ Set.Icc ((4003 / 64000) : ℝ) (4019 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((566627345357 / 500000000000) : ℝ) ≤ Real.exp (2 * (4003 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4003 / 64000)) (566627345357 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4019 / 64000) : ℝ)) ≤ (56691072987 / 50000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4019 / 64000)) (56691072987 / 50000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((243679957 / 125000000) : ℝ) ≤ Real.exp (3 * (356022387 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (356022387 / 100000000) / 16) (243679957 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1781002781 / 500000000) : ℝ) / 16) ≤ (195009101 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1781002781 / 500000000) / 16) (195009101 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4003 / 64000) : ℝ) (4019 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (356022387 / 100000000) (1781002781 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4003 / 64000) (4019 / 64000) (566627345357 / 500000000000) (56691072987 / 50000000000) (356022387 / 100000000) (1781002781 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4003 / 64000) (4019 / 64000) (356022387 / 100000000) (1781002781 / 500000000) (4572481 / 200000000000) (11492467 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (356022387 / 100000000) (1781002781 / 500000000) (243679957 / 125000000) (195009101 / 100000000) (4572481 / 200000000000) (11492467 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0913 :
    ∀ t ∈ Set.Icc ((4019 / 64000) : ℝ) (807 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1133821459739 / 1000000000000) : ℝ) ≤ Real.exp (2 * (4019 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4019 / 64000)) (1133821459739 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((807 / 12800) : ℝ)) ≤ (567194256111 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (807 / 12800)) (567194256111 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((975045297 / 500000000) : ℝ) ≤ Real.exp (3 * (3562004427 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3562004427 / 1000000000) / 16) (975045297 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((356378701 / 100000000) : ℝ) / 16) ≤ (1950742491 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (356378701 / 100000000) / 16) (1950742491 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4019 / 64000) : ℝ) (807 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3562004427 / 1000000000) (356378701 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4019 / 64000) (807 / 12800) (1133821459739 / 1000000000000) (567194256111 / 500000000000) (3562004427 / 1000000000) (356378701 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4019 / 64000) (807 / 12800) (3562004427 / 1000000000) (356378701 / 100000000) (11370273 / 500000000000) (5715621 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3562004427 / 1000000000) (356378701 / 100000000) (975045297 / 500000000) (1950742491 / 1000000000) (11370273 / 500000000000) (5715621 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0914 :
    ∀ t ∈ Set.Icc ((807 / 12800) : ℝ) (4051 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1134388512221 / 1000000000000) : ℝ) ≤ Real.exp (2 * (807 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (807 / 12800)) (1134388512221 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4051 / 64000) : ℝ)) ≤ (11349558483 / 10000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4051 / 64000)) (11349558483 / 10000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((975371037 / 500000000) : ℝ) ≤ Real.exp (3 * (1781892937 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1781892937 / 500000000) / 16) (975371037 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3565569349 / 1000000000) : ℝ) / 16) ≤ (487848629 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3565569349 / 1000000000) / 16) (487848629 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((807 / 12800) : ℝ) (4051 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1781892937 / 500000000) (3565569349 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (807 / 12800) (4051 / 64000) (1134388512221 / 1000000000000) (11349558483 / 10000000000) (1781892937 / 500000000) (3565569349 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (807 / 12800) (4051 / 64000) (1781892937 / 500000000) (3565569349 / 1000000000) (5654819 / 250000000000) (7277 / 320000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1781892937 / 500000000) (3565569349 / 1000000000) (975371037 / 500000000) (487848629 / 250000000) (5654819 / 250000000000) (7277 / 320000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0915 :
    ∀ t ∈ Set.Icc ((4051 / 64000) : ℝ) (4067 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1134955848299 / 1000000000000) : ℝ) ≤ Real.exp (2 * (4051 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4051 / 64000)) (1134955848299 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4067 / 64000) : ℝ)) ≤ (1135523468117 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4067 / 64000)) (1135523468117 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1951394099 / 1000000000) : ℝ) ≤ Real.exp (3 * (3565568213 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3565568213 / 1000000000) / 16) (1951394099 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3567352579 / 1000000000) : ℝ) / 16) ≤ (488011771 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3567352579 / 1000000000) / 16) (488011771 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4051 / 64000) : ℝ) (4067 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3565568213 / 1000000000) (3567352579 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4051 / 64000) (4067 / 64000) (1134955848299 / 1000000000000) (1135523468117 / 1000000000000) (3565568213 / 1000000000) (3567352579 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4051 / 64000) (4067 / 64000) (3565568213 / 1000000000) (3567352579 / 1000000000) (11249297 / 500000000000) (4523871 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3565568213 / 1000000000) (3567352579 / 1000000000) (1951394099 / 1000000000) (488011771 / 250000000) (11249297 / 500000000000) (4523871 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0916 :
    ∀ t ∈ Set.Icc ((4067 / 64000) : ℝ) (4083 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((283880867029 / 250000000000) : ℝ) ≤ Real.exp (2 * (4067 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4067 / 64000)) (283880867029 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4083 / 64000) : ℝ)) ≤ (227218274363 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4083 / 64000)) (227218274363 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((488011667 / 250000000) : ℝ) ≤ Real.exp (3 * (3567351443 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3567351443 / 1000000000) / 16) (488011667 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1784568351 / 500000000) : ℝ) / 16) ≤ (976350099 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1784568351 / 500000000) / 16) (976350099 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4067 / 64000) : ℝ) (4083 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3567351443 / 1000000000) (1784568351 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4067 / 64000) (4083 / 64000) (283880867029 / 250000000000) (227218274363 / 200000000000) (3567351443 / 1000000000) (1784568351 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4067 / 64000) (4083 / 64000) (3567351443 / 1000000000) (1784568351 / 500000000) (11189247 / 500000000000) (22498671 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3567351443 / 1000000000) (1784568351 / 500000000) (488011667 / 250000000) (976350099 / 500000000) (11189247 / 500000000000) (22498671 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0917 :
    ∀ t ∈ Set.Icc ((4083 / 64000) : ℝ) (4099 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((568045685907 / 500000000000) : ℝ) ≤ Real.exp (2 * (4083 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4083 / 64000)) (568045685907 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4099 / 64000) : ℝ)) ≤ (71041222471 / 62500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4099 / 64000)) (71041222471 / 62500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1952699781 / 1000000000) : ℝ) ≤ Real.exp (3 * (892283891 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (892283891 / 250000000) / 16) (1952699781 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((892730429 / 250000000) : ℝ) / 16) ≤ (1953353857 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (892730429 / 250000000) / 16) (1953353857 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4083 / 64000) : ℝ) (4099 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (892283891 / 250000000) (892730429 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4083 / 64000) (4099 / 64000) (568045685907 / 500000000000) (71041222471 / 62500000000) (892283891 / 250000000) (892730429 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4083 / 64000) (4099 / 64000) (892283891 / 250000000) (892730429 / 250000000) (22258977 / 1000000000000) (5594643 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (892283891 / 250000000) (892730429 / 250000000) (1952699781 / 1000000000) (1953353857 / 1000000000) (22258977 / 1000000000000) (5594643 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0918 :
    ∀ t ∈ Set.Icc ((4099 / 64000) : ℝ) (823 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((227331911907 / 200000000000) : ℝ) ≤ Real.exp (2 * (4099 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (4099 / 64000)) (227331911907 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((823 / 12800) : ℝ)) ≤ (568614015711 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (823 / 12800)) (568614015711 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1953353439 / 1000000000) : ℝ) ≤ Real.exp (3 * (1785460289 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1785460289 / 500000000) / 16) (1953353439 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3572707623 / 1000000000) : ℝ) / 16) ≤ (977004031 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3572707623 / 1000000000) / 16) (977004031 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((4099 / 64000) : ℝ) (823 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1785460289 / 500000000) (3572707623 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (4099 / 64000) (823 / 12800) (227331911907 / 200000000000) (568614015711 / 500000000000) (1785460289 / 500000000) (3572707623 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (4099 / 64000) (823 / 12800) (1785460289 / 500000000) (3572707623 / 1000000000) (11070019 / 500000000000) (11129527 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1785460289 / 500000000) (3572707623 / 1000000000) (1953353439 / 1000000000) (977004031 / 500000000) (11070019 / 500000000000) (11129527 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0919 :
    ∀ t ∈ Set.Icc ((823 / 12800) : ℝ) (4131 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1137228031421 / 1000000000000) : ℝ) ≤ Real.exp (2 * (823 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (823 / 12800)) (1137228031421 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((4131 / 64000) : ℝ)) ≤ (227559357523 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (4131 / 64000)) (227559357523 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((488501911 / 250000000) : ℝ) ≤ Real.exp (3 * (714541297 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (714541297 / 200000000) / 16) (488501911 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((446811803 / 125000000) : ℝ) / 16) ≤ (977331407 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (446811803 / 125000000) / 16) (977331407 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((823 / 12800) : ℝ) (4131 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (714541297 / 200000000) (446811803 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (823 / 12800) (4131 / 64000) (1137228031421 / 1000000000000) (227559357523 / 200000000000) (714541297 / 200000000) (446811803 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (823 / 12800) (4131 / 64000) (714541297 / 200000000) (446811803 / 125000000) (5505419 / 250000000000) (4428023 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (714541297 / 200000000) (446811803 / 125000000) (488501911 / 250000000) (977331407 / 500000000) (5505419 / 250000000000) (4428023 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch045 :
    ∀ t ∈ Set.Icc ((3811 / 64000) : ℝ) (4131 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0900
      hpThetaDensityTwoTermCompact_cell0901)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0902
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0903
      hpThetaDensityTwoTermCompact_cell0904)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0905
      hpThetaDensityTwoTermCompact_cell0906)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0907
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0908
      hpThetaDensityTwoTermCompact_cell0909))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0910
      hpThetaDensityTwoTermCompact_cell0911)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0912
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0913
      hpThetaDensityTwoTermCompact_cell0914)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0915
      hpThetaDensityTwoTermCompact_cell0916)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0917
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0918
      hpThetaDensityTwoTermCompact_cell0919)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch045
end HodgeProofHP
