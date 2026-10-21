/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0860 :
    ∀ t ∈ Set.Icc ((3339 / 64000) : ℝ) (3347 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((277495486409 / 250000000000) : ℝ) ≤ Real.exp (2 * (3339 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3339 / 64000)) (277495486409 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3347 / 64000) : ℝ)) ≤ (555129737907 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3347 / 64000)) (555129737907 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1922897571 / 1000000000) : ℝ) ≤ Real.exp (3 * (544861 / 156250) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (544861 / 156250) / 16) (1922897571 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1743991699 / 500000000) : ℝ) / 16) ≤ (1923212351 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1743991699 / 500000000) / 16) (1923212351 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3339 / 64000) : ℝ) (3347 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (544861 / 156250) (1743991699 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3339 / 64000) (3347 / 64000) (277495486409 / 250000000000) (555129737907 / 500000000000) (544861 / 156250) (1743991699 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3339 / 64000) (3347 / 64000) (544861 / 156250) (1743991699 / 500000000) (14273621 / 500000000000) (28622107 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (544861 / 156250) (1743991699 / 500000000) (1922897571 / 1000000000) (1923212351 / 1000000000) (14273621 / 500000000000) (28622107 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0861 :
    ∀ t ∈ Set.Icc ((3347 / 64000) : ℝ) (671 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1110259475813 / 1000000000000) : ℝ) ≤ Real.exp (2 * (3347 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3347 / 64000)) (1110259475813 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((671 / 12800) : ℝ)) ≤ (1110537075381 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (671 / 12800)) (1110537075381 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1923211949 / 1000000000) : ℝ) ≤ Real.exp (3 * (3487982287 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3487982287 / 1000000000) / 16) (1923211949 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3488855503 / 1000000000) : ℝ) / 16) ≤ (96176343 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3488855503 / 1000000000) / 16) (96176343 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3347 / 64000) : ℝ) (671 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3487982287 / 1000000000) (3488855503 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3347 / 64000) (671 / 12800) (1110259475813 / 1000000000000) (1110537075381 / 1000000000000) (3487982287 / 1000000000) (3488855503 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3347 / 64000) (671 / 12800) (3487982287 / 1000000000) (3488855503 / 1000000000) (28472651 / 1000000000000) (28547339 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3487982287 / 1000000000) (3488855503 / 1000000000) (1923211949 / 1000000000) (96176343 / 50000000) (28472651 / 1000000000000) (28547339 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0862 :
    ∀ t ∈ Set.Icc ((671 / 12800) : ℝ) (3363 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((55526853769 / 50000000000) : ℝ) ≤ Real.exp (2 * (671 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (671 / 12800)) (55526853769 / 50000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3363 / 64000) : ℝ)) ≤ (1110814744357 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3363 / 64000)) (1110814744357 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((961763229 / 500000000) : ℝ) ≤ Real.exp (3 * (3488854391 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3488854391 / 1000000000) / 16) (961763229 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1744863913 / 500000000) : ℝ) / 16) ≤ (1923841499 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1744863913 / 500000000) / 16) (1923841499 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((671 / 12800) : ℝ) (3363 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3488854391 / 1000000000) (1744863913 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (671 / 12800) (3363 / 64000) (55526853769 / 50000000000) (1110814744357 / 1000000000000) (3488854391 / 1000000000) (1744863913 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (671 / 12800) (3363 / 64000) (3488854391 / 1000000000) (1744863913 / 500000000) (28398237 / 1000000000000) (7118187 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3488854391 / 1000000000) (1744863913 / 500000000) (961763229 / 500000000) (1923841499 / 1000000000) (28398237 / 1000000000000) (7118187 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0863 :
    ∀ t ∈ Set.Icc ((3363 / 64000) : ℝ) (3371 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((277703686089 / 250000000000) : ℝ) ≤ Real.exp (2 * (3363 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3363 / 64000)) (277703686089 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3371 / 64000) : ℝ)) ≤ (1111092482759 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3371 / 64000)) (1111092482759 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((240480137 / 125000000) : ℝ) ≤ Real.exp (3 * (1744863357 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1744863357 / 500000000) / 16) (240480137 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3490600367 / 1000000000) : ℝ) / 16) ≤ (481039067 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3490600367 / 1000000000) / 16) (481039067 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3363 / 64000) : ℝ) (3371 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1744863357 / 500000000) (3490600367 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3363 / 64000) (3371 / 64000) (277703686089 / 250000000000) (1111092482759 / 1000000000000) (1744863357 / 500000000) (3490600367 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3363 / 64000) (3371 / 64000) (1744863357 / 500000000) (3490600367 / 1000000000) (14161999 / 500000000000) (28398333 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1744863357 / 500000000) (3490600367 / 1000000000) (240480137 / 125000000) (481039067 / 250000000) (14161999 / 500000000000) (28398333 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0864 :
    ∀ t ∈ Set.Icc ((3371 / 64000) : ℝ) (3379 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((555546241379 / 500000000000) : ℝ) ≤ Real.exp (2 * (3371 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3371 / 64000)) (555546241379 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3379 / 64000) : ℝ)) ≤ (277842572651 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3379 / 64000)) (277842572651 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((384831173 / 200000000) : ℝ) ≤ Real.exp (3 * (698119851 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (698119851 / 200000000) / 16) (384831173 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1745736563 / 500000000) : ℝ) / 16) ≤ (1924471167 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1745736563 / 500000000) / 16) (1924471167 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3371 / 64000) : ℝ) (3379 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (698119851 / 200000000) (1745736563 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3371 / 64000) (3379 / 64000) (555546241379 / 500000000000) (277842572651 / 250000000000) (698119851 / 200000000) (1745736563 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3371 / 64000) (3379 / 64000) (698119851 / 200000000) (1745736563 / 500000000) (5649987 / 200000000000) (14162047 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (698119851 / 200000000) (1745736563 / 500000000) (384831173 / 200000000) (1924471167 / 1000000000) (5649987 / 200000000000) (14162047 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0865 :
    ∀ t ∈ Set.Icc ((3379 / 64000) : ℝ) (3387 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1111370290603 / 1000000000000) : ℝ) ≤ Real.exp (2 * (3379 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3379 / 64000)) (1111370290603 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3387 / 64000) : ℝ)) ≤ (111164816791 / 100000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3387 / 64000)) (111164816791 / 100000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((481117691 / 250000000) : ℝ) ≤ Real.exp (3 * (3491472013 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3491472013 / 1000000000) / 16) (481117691 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3492346103 / 1000000000) : ℝ) / 16) ≤ (481196549 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3492346103 / 1000000000) / 16) (481196549 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3379 / 64000) : ℝ) (3387 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3491472013 / 1000000000) (3492346103 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3379 / 64000) (3387 / 64000) (1111370290603 / 1000000000000) (111164816791 / 100000000000) (3491472013 / 1000000000) (3492346103 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3379 / 64000) (3387 / 64000) (3491472013 / 1000000000) (3492346103 / 1000000000) (28176047 / 1000000000000) (28250031 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3491472013 / 1000000000) (3492346103 / 1000000000) (481117691 / 250000000) (481196549 / 250000000) (28176047 / 1000000000000) (28250031 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0866 :
    ∀ t ∈ Set.Icc ((3387 / 64000) : ℝ) (679 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1111648167909 / 1000000000000) : ℝ) ≤ Real.exp (2 * (3387 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3387 / 64000)) (1111648167909 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((679 / 12800) : ℝ)) ≤ (555963057347 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (679 / 12800)) (555963057347 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((962392897 / 500000000) : ℝ) ≤ Real.exp (3 * (3492344991 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3492344991 / 1000000000) / 16) (962392897 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3493219299 / 1000000000) : ℝ) / 16) ≤ (481275339 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3493219299 / 1000000000) / 16) (481275339 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3387 / 64000) : ℝ) (679 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3492344991 / 1000000000) (3493219299 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3387 / 64000) (679 / 12800) (1111648167909 / 1000000000000) (555963057347 / 500000000000) (3492344991 / 1000000000) (3493219299 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3387 / 64000) (679 / 12800) (3492344991 / 1000000000) (3493219299 / 1000000000) (14051167 / 500000000000) (14088071 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3492344991 / 1000000000) (3493219299 / 1000000000) (962392897 / 500000000) (481275339 / 250000000) (14051167 / 500000000000) (14088071 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0867 :
    ∀ t ∈ Set.Icc ((679 / 12800) : ℝ) (3403 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1111926114693 / 1000000000000) : ℝ) ≤ Real.exp (2 * (679 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (679 / 12800)) (1111926114693 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3403 / 64000) : ℝ)) ≤ (1112204130973 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3403 / 64000)) (1112204130973 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1925100953 / 1000000000) : ℝ) ≤ Real.exp (3 * (1746609093 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1746609093 / 500000000) / 16) (1925100953 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3494092713 / 1000000000) : ℝ) / 16) ≤ (962708323 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3494092713 / 1000000000) / 16) (962708323 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((679 / 12800) : ℝ) (3403 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1746609093 / 500000000) (3494092713 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (679 / 12800) (3403 / 64000) (1111926114693 / 1000000000000) (1112204130973 / 1000000000000) (1746609093 / 500000000) (3494092713 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (679 / 12800) (3403 / 64000) (1746609093 / 500000000) (3494092713 / 1000000000) (7007199 / 250000000000) (28102429 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1746609093 / 500000000) (3494092713 / 1000000000) (1925100953 / 1000000000) (962708323 / 500000000) (7007199 / 250000000000) (28102429 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0868 :
    ∀ t ∈ Set.Icc ((3403 / 64000) : ℝ) (3411 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((278051032743 / 250000000000) : ℝ) ≤ Real.exp (2 * (3403 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3403 / 64000)) (278051032743 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3411 / 64000) : ℝ)) ≤ (222496443353 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3411 / 64000)) (222496443353 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1925416243 / 1000000000) : ℝ) ≤ Real.exp (3 * (8735229 / 2500000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (8735229 / 2500000) / 16) (1925416243 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((698993269 / 200000000) : ℝ) / 16) ≤ (1925732067 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (698993269 / 200000000) / 16) (1925732067 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3403 / 64000) : ℝ) (3411 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (8735229 / 2500000) (698993269 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3403 / 64000) (3411 / 64000) (278051032743 / 250000000000) (222496443353 / 200000000000) (8735229 / 2500000) (698993269 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3403 / 64000) (3411 / 64000) (8735229 / 2500000) (698993269 / 200000000) (27955431 / 1000000000000) (28028891 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (8735229 / 2500000) (698993269 / 200000000) (1925416243 / 1000000000) (1925732067 / 1000000000) (27955431 / 1000000000000) (28028891 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0869 :
    ∀ t ∈ Set.Icc ((3411 / 64000) : ℝ) (3419 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((278120554191 / 250000000000) : ℝ) ≤ Real.exp (2 * (3411 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3411 / 64000)) (278120554191 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3419 / 64000) : ℝ)) ≤ (1112760372087 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3419 / 64000)) (1112760372087 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((120358229 / 62500000) : ℝ) ≤ Real.exp (3 * (218435327 / 62500000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (218435327 / 62500000) / 16) (120358229 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((873960049 / 250000000) : ℝ) / 16) ≤ (963023809 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (873960049 / 250000000) / 16) (963023809 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3411 / 64000) : ℝ) (3419 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (218435327 / 62500000) (873960049 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3411 / 64000) (3419 / 64000) (278120554191 / 250000000000) (1112760372087 / 1000000000000) (218435327 / 62500000) (873960049 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3411 / 64000) (3419 / 64000) (218435327 / 62500000) (873960049 / 250000000) (27882241 / 1000000000000) (13977763 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (218435327 / 62500000) (873960049 / 250000000) (120358229 / 62500000) (963023809 / 500000000) (27882241 / 1000000000000) (13977763 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0870 :
    ∀ t ∈ Set.Icc ((3419 / 64000) : ℝ) (3427 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((556380186043 / 500000000000) : ℝ) ≤ Real.exp (2 * (3419 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3419 / 64000)) (556380186043 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3427 / 64000) : ℝ)) ≤ (1113038596957 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3427 / 64000)) (1113038596957 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((385209443 / 200000000) : ℝ) ≤ Real.exp (3 * (1747919541 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1747919541 / 500000000) / 16) (385209443 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((699342853 / 200000000) : ℝ) / 16) ≤ (19263633 / 10000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (699342853 / 200000000) / 16) (19263633 / 10000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3419 / 64000) : ℝ) (3427 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1747919541 / 500000000) (699342853 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3419 / 64000) (3427 / 64000) (556380186043 / 500000000000) (1113038596957 / 1000000000000) (1747919541 / 500000000) (699342853 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3419 / 64000) (3427 / 64000) (1747919541 / 500000000) (699342853 / 200000000) (27809223 / 1000000000000) (5576467 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1747919541 / 500000000) (699342853 / 200000000) (385209443 / 200000000) (19263633 / 10000000) (27809223 / 1000000000000) (5576467 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0871 :
    ∀ t ∈ Set.Icc ((3427 / 64000) : ℝ) (687 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((278259649239 / 250000000000) : ℝ) ≤ Real.exp (2 * (3427 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3427 / 64000)) (278259649239 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((687 / 12800) : ℝ)) ≤ (4348894107 / 3906250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (687 / 12800)) (4348894107 / 3906250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1926362897 / 1000000000) : ℝ) ≤ Real.exp (3 * (3496713151 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3496713151 / 1000000000) / 16) (1926362897 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3497588553 / 1000000000) : ℝ) / 16) ≤ (1926679113 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3497588553 / 1000000000) / 16) (1926679113 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3427 / 64000) : ℝ) (687 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3496713151 / 1000000000) (3497588553 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3427 / 64000) (687 / 12800) (278259649239 / 250000000000) (4348894107 / 3906250000) (3496713151 / 1000000000) (3497588553 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3427 / 64000) (687 / 12800) (3496713151 / 1000000000) (3497588553 / 1000000000) (27736379 / 1000000000000) (27809317 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3496713151 / 1000000000) (3497588553 / 1000000000) (1926362897 / 1000000000) (1926679113 / 1000000000) (27736379 / 1000000000000) (27809317 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0872 :
    ∀ t ∈ Set.Icc ((687 / 12800) : ℝ) (3443 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1113316891391 / 1000000000000) : ℝ) ≤ Real.exp (2 * (687 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (687 / 12800)) (1113316891391 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3443 / 64000) : ℝ)) ≤ (1113595255409 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3443 / 64000)) (1113595255409 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1926678709 / 1000000000) : ℝ) ≤ Real.exp (3 * (3497587439 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3497587439 / 1000000000) / 16) (1926678709 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((174923153 / 50000000) : ℝ) / 16) ≤ (120437191 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (174923153 / 50000000) / 16) (120437191 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((687 / 12800) : ℝ) (3443 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3497587439 / 1000000000) (174923153 / 50000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (687 / 12800) (3443 / 64000) (1113316891391 / 1000000000000) (1113595255409 / 1000000000000) (3497587439 / 1000000000) (174923153 / 50000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (687 / 12800) (3443 / 64000) (3497587439 / 1000000000) (174923153 / 50000000) (6915927 / 250000000000) (27736473 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3497587439 / 1000000000) (174923153 / 50000000) (1926678709 / 1000000000) (120437191 / 62500000) (6915927 / 250000000000) (27736473 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0873 :
    ∀ t ∈ Set.Icc ((3443 / 64000) : ℝ) (3451 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((69599703463 / 62500000000) : ℝ) ≤ Real.exp (2 * (3443 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3443 / 64000)) (69599703463 / 62500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3451 / 64000) : ℝ)) ≤ (44554947561 / 40000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3451 / 64000)) (44554947561 / 40000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1926994653 / 1000000000) : ℝ) ≤ Real.exp (3 * (699692389 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (699692389 / 200000000) / 16) (1926994653 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((699867557 / 200000000) : ℝ) / 16) ≤ (1927311131 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (699867557 / 200000000) / 16) (1927311131 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3443 / 64000) : ℝ) (3451 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (699692389 / 200000000) (699867557 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3443 / 64000) (3451 / 64000) (69599703463 / 62500000000) (44554947561 / 40000000000) (699692389 / 200000000) (699867557 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3443 / 64000) (3451 / 64000) (699692389 / 200000000) (699867557 / 200000000) (3448901 / 125000000000) (27663801 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (699692389 / 200000000) (699867557 / 200000000) (1926994653 / 1000000000) (1927311131 / 1000000000) (3448901 / 125000000000) (27663801 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0874 :
    ∀ t ∈ Set.Icc ((3451 / 64000) : ℝ) (3459 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((17404276391 / 15625000000) : ℝ) ≤ Real.exp (2 * (3451 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3451 / 64000)) (17404276391 / 15625000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3459 / 64000) : ℝ)) ≤ (1114152192259 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3459 / 64000)) (1114152192259 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1927310727 / 1000000000) : ℝ) ≤ Real.exp (3 * (349933667 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (349933667 / 100000000) / 16) (1927310727 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3500212729 / 1000000000) : ℝ) / 16) ≤ (240953417 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3500212729 / 1000000000) / 16) (240953417 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3451 / 64000) : ℝ) (3459 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (349933667 / 100000000) (3500212729 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3451 / 64000) (3459 / 64000) (17404276391 / 15625000000) (1114152192259 / 1000000000000) (349933667 / 100000000) (3500212729 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3451 / 64000) (3459 / 64000) (349933667 / 100000000) (3500212729 / 1000000000) (27518881 / 1000000000000) (13795651 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (349933667 / 100000000) (3500212729 / 1000000000) (1927310727 / 1000000000) (240953417 / 125000000) (27518881 / 1000000000000) (13795651 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0875 :
    ∀ t ∈ Set.Icc ((3459 / 64000) : ℝ) (3467 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((557076096129 / 500000000000) : ℝ) ≤ Real.exp (2 * (3459 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3459 / 64000)) (557076096129 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3467 / 64000) : ℝ)) ≤ (1114430765127 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3467 / 64000)) (1114430765127 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1927626931 / 1000000000) : ℝ) ≤ Real.exp (3 * (3500211613 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3500211613 / 1000000000) / 16) (1927626931 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3501087891 / 1000000000) : ℝ) / 16) ≤ (240992959 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3501087891 / 1000000000) / 16) (240992959 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3459 / 64000) : ℝ) (3467 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3500211613 / 1000000000) (3501087891 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3459 / 64000) (3467 / 64000) (557076096129 / 500000000000) (1114430765127 / 1000000000000) (3500211613 / 1000000000) (3501087891 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3459 / 64000) (3467 / 64000) (3500211613 / 1000000000) (3501087891 / 1000000000) (1097869 / 40000000000) (13759487 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3500211613 / 1000000000) (3501087891 / 1000000000) (1927626931 / 1000000000) (240992959 / 125000000) (1097869 / 40000000000) (13759487 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0876 :
    ∀ t ∈ Set.Icc ((3467 / 64000) : ℝ) (139 / 2560), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((557215382563 / 500000000000) : ℝ) ≤ Real.exp (2 * (3467 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3467 / 64000)) (557215382563 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((139 / 2560) : ℝ)) ≤ (1114709407647 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (139 / 2560)) (1114709407647 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((481985817 / 250000000) : ℝ) ≤ Real.exp (3 * (437635847 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (437635847 / 125000000) / 16) (481985817 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3501963273 / 1000000000) : ℝ) / 16) ≤ (1928260139 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3501963273 / 1000000000) / 16) (1928260139 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3467 / 64000) : ℝ) (139 / 2560),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (437635847 / 125000000) (3501963273 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3467 / 64000) (139 / 2560) (557215382563 / 500000000000) (1114709407647 / 1000000000000) (437635847 / 125000000) (3501963273 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3467 / 64000) (139 / 2560) (437635847 / 125000000) (3501963273 / 1000000000) (27374741 / 1000000000000) (13723409 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (437635847 / 125000000) (3501963273 / 1000000000) (481985817 / 250000000) (1928260139 / 1000000000) (27374741 / 1000000000000) (13723409 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0877 :
    ∀ t ∈ Set.Icc ((139 / 2560) : ℝ) (3483 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((557354703823 / 500000000000) : ℝ) ≤ Real.exp (2 * (139 / 2560)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (139 / 2560)) (557354703823 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3483 / 64000) : ℝ)) ≤ (1114988119837 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3483 / 64000)) (1114988119837 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((964129867 / 500000000) : ℝ) ≤ Real.exp (3 * (3501962157 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3501962157 / 1000000000) / 16) (964129867 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3502838873 / 1000000000) : ℝ) / 16) ≤ (1928576737 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3502838873 / 1000000000) / 16) (1928576737 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((139 / 2560) : ℝ) (3483 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3501962157 / 1000000000) (3502838873 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (139 / 2560) (3483 / 64000) (557354703823 / 500000000000) (1114988119837 / 1000000000000) (3501962157 / 1000000000) (3502838873 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (139 / 2560) (3483 / 64000) (3501962157 / 1000000000) (3502838873 / 1000000000) (27302927 / 1000000000000) (13687417 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3501962157 / 1000000000) (3502838873 / 1000000000) (964129867 / 500000000) (1928576737 / 1000000000) (27302927 / 1000000000000) (13687417 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0878 :
    ∀ t ∈ Set.Icc ((3483 / 64000) : ℝ) (3491 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((278747029959 / 250000000000) : ℝ) ≤ Real.exp (2 * (3483 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3483 / 64000)) (278747029959 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3491 / 64000) : ℝ)) ≤ (1115266901713 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3491 / 64000)) (1115266901713 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1928576333 / 1000000000) : ℝ) ≤ Real.exp (3 * (3502837757 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3502837757 / 1000000000) / 16) (1928576333 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((875928673 / 250000000) : ℝ) / 16) ≤ (964446733 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (875928673 / 250000000) / 16) (964446733 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3483 / 64000) : ℝ) (3491 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3502837757 / 1000000000) (875928673 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3483 / 64000) (3491 / 64000) (278747029959 / 250000000000) (1115266901713 / 1000000000000) (3502837757 / 1000000000) (875928673 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3483 / 64000) (3491 / 64000) (3502837757 / 1000000000) (875928673 / 250000000) (6807821 / 250000000000) (1365151 / 50000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3502837757 / 1000000000) (875928673 / 250000000) (1928576333 / 1000000000) (964446733 / 500000000) (6807821 / 250000000000) (1365151 / 50000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0879 :
    ∀ t ∈ Set.Icc ((3491 / 64000) : ℝ) (3499 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((69704181357 / 62500000000) : ℝ) ≤ Real.exp (2 * (3491 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3491 / 64000)) (69704181357 / 62500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3499 / 64000) : ℝ)) ≤ (1115545753293 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3499 / 64000)) (1115545753293 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((964446531 / 500000000) : ℝ) ≤ Real.exp (3 * (437964197 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (437964197 / 125000000) / 16) (964446531 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((350459073 / 100000000) : ℝ) / 16) ≤ (1929210327 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (350459073 / 100000000) / 16) (1929210327 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3491 / 64000) : ℝ) (3499 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (437964197 / 125000000) (350459073 / 100000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (3491 / 64000) (3499 / 64000) (69704181357 / 62500000000) (1115545753293 / 1000000000000) (437964197 / 125000000) (350459073 / 100000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (3491 / 64000) (3499 / 64000) (437964197 / 125000000) (350459073 / 100000000) (27159811 / 1000000000000) (1701961 / 62500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (437964197 / 125000000) (350459073 / 100000000) (964446531 / 500000000) (1929210327 / 1000000000) (27159811 / 1000000000000) (1701961 / 62500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch043 :
    ∀ t ∈ Set.Icc ((3339 / 64000) : ℝ) (3499 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0860
      hpThetaDensityTwoTermCompact_cell0861)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0862
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0863
      hpThetaDensityTwoTermCompact_cell0864)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0865
      hpThetaDensityTwoTermCompact_cell0866)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0867
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0868
      hpThetaDensityTwoTermCompact_cell0869))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0870
      hpThetaDensityTwoTermCompact_cell0871)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0872
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0873
      hpThetaDensityTwoTermCompact_cell0874)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0875
      hpThetaDensityTwoTermCompact_cell0876)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0877
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0878
      hpThetaDensityTwoTermCompact_cell0879)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch043
end HodgeProofHP
