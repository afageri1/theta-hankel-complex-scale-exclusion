/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityTwoTermCellCriterion

noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0340 :
    ∀ t ∈ Set.Icc ((1589 / 64000) : ℝ) (159 / 6400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((26272744601 / 25000000000) : ℝ) ≤ Real.exp (2 * (1589 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1589 / 64000)) (26272744601 / 25000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((159 / 6400) : ℝ)) ≤ (210188525097 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (159 / 6400)) (210188525097 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1857138443 / 1000000000) : ℝ) ≤ Real.exp (3 * (330152977 / 100000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (330152977 / 100000000) / 16) (1857138443 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((825408499 / 250000000) : ℝ) / 16) ≤ (1857174737 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (825408499 / 250000000) / 16) (1857174737 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1589 / 64000) : ℝ) (159 / 6400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (330152977 / 100000000) (825408499 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1589 / 64000) (159 / 6400) (26272744601 / 25000000000) (210188525097 / 200000000000) (330152977 / 100000000) (825408499 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1589 / 64000) (159 / 6400) (330152977 / 100000000) (825408499 / 250000000) (3120583 / 62500000000) (49944943 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (330152977 / 100000000) (825408499 / 250000000) (1857138443 / 1000000000) (1857174737 / 1000000000) (3120583 / 62500000000) (49944943 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0341 :
    ∀ t ∈ Set.Icc ((159 / 6400) : ℝ) (1591 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((262735656371 / 250000000000) : ℝ) ≤ Real.exp (2 * (159 / 6400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (159 / 6400)) (262735656371 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1591 / 64000) : ℝ)) ≤ (210195093591 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1591 / 64000)) (210195093591 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((185717437 / 100000000) : ℝ) ≤ Real.exp (3 * (206352059 / 62500000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (206352059 / 62500000) / 16) (185717437 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1650868587 / 500000000) : ℝ) / 16) ≤ (928605333 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1650868587 / 500000000) / 16) (928605333 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((159 / 6400) : ℝ) (1591 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (206352059 / 62500000) (1650868587 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (159 / 6400) (1591 / 64000) (262735656371 / 250000000000) (210195093591 / 200000000000) (206352059 / 62500000) (1650868587 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (159 / 6400) (1591 / 64000) (206352059 / 62500000) (1650868587 / 500000000) (399311 / 8000000000) (49929487 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (206352059 / 62500000) (1650868587 / 500000000) (185717437 / 100000000) (928605333 / 500000000) (399311 / 8000000000) (49929487 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0342 :
    ∀ t ∈ Set.Icc ((1591 / 64000) : ℝ) (199 / 8000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((525487733977 / 500000000000) : ℝ) ≤ Real.exp (2 * (1591 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1591 / 64000)) (525487733977 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((199 / 8000) : ℝ)) ≤ (262752077863 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (199 / 8000)) (262752077863 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1857210299 / 1000000000) : ℝ) ≤ Real.exp (3 * (1650868061 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1650868061 / 500000000) / 16) (1857210299 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((660368071 / 200000000) : ℝ) / 16) ≤ (1857246597 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (660368071 / 200000000) / 16) (1857246597 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1591 / 64000) : ℝ) (199 / 8000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1650868061 / 500000000) (660368071 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1591 / 64000) (199 / 8000) (525487733977 / 500000000000) (262752077863 / 250000000000) (1650868061 / 500000000) (660368071 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1591 / 64000) (199 / 8000) (1650868061 / 500000000) (660368071 / 200000000) (49898427 / 1000000000000) (24957017 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1650868061 / 500000000) (660368071 / 200000000) (1857210299 / 1000000000) (1857246597 / 1000000000) (49898427 / 1000000000000) (24957017 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0343 :
    ∀ t ∈ Set.Icc ((199 / 8000) : ℝ) (1593 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1051008311451 / 1000000000000) : ℝ) ≤ Real.exp (2 * (199 / 8000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (199 / 8000)) (1051008311451 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1593 / 64000) : ℝ)) ≤ (42041646239 / 40000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1593 / 64000)) (42041646239 / 40000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((185724623 / 100000000) : ℝ) ≤ Real.exp (3 * (3301839303 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3301839303 / 1000000000) / 16) (185724623 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3301943539 / 1000000000) : ℝ) / 16) ≤ (185728253 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3301943539 / 1000000000) / 16) (185728253 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((199 / 8000) : ℝ) (1593 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3301839303 / 1000000000) (3301943539 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (199 / 8000) (1593 / 64000) (1051008311451 / 1000000000000) (42041646239 / 40000000000) (3301839303 / 1000000000) (3301943539 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (199 / 8000) (1593 / 64000) (3301839303 / 1000000000) (3301943539 / 1000000000) (49882983 / 1000000000000) (24949293 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3301839303 / 1000000000) (3301943539 / 1000000000) (185724623 / 100000000) (185728253 / 100000000) (49882983 / 1000000000000) (24949293 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0344 :
    ∀ t ∈ Set.Icc ((1593 / 64000) : ℝ) (797 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((525520577987 / 500000000000) : ℝ) ≤ Real.exp (2 * (1593 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1593 / 64000)) (525520577987 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((797 / 32000) : ℝ)) ≤ (262768500381 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (797 / 32000)) (262768500381 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((928641081 / 500000000) : ℝ) ≤ Real.exp (3 * (3301942487 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3301942487 / 1000000000) / 16) (928641081 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1651023363 / 500000000) : ℝ) / 16) ≤ (29020601 / 15625000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1651023363 / 500000000) / 16) (29020601 / 15625000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1593 / 64000) : ℝ) (797 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3301942487 / 1000000000) (1651023363 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1593 / 64000) (797 / 32000) (525520577987 / 500000000000) (262768500381 / 250000000000) (3301942487 / 1000000000) (1651023363 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1593 / 64000) (797 / 32000) (3301942487 / 1000000000) (1651023363 / 500000000) (6233443 / 125000000000) (24941571 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3301942487 / 1000000000) (1651023363 / 500000000) (928641081 / 500000000) (29020601 / 15625000) (6233443 / 125000000000) (24941571 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0345 :
    ∀ t ∈ Set.Icc ((797 / 32000) : ℝ) (319 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1051074001523 / 1000000000000) : ℝ) ≤ Real.exp (2 * (797 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (797 / 32000)) (1051074001523 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((319 / 12800) : ℝ)) ≤ (10511068481 / 10000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (319 / 12800)) (10511068481 / 10000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((116082381 / 62500000) : ℝ) ≤ Real.exp (3 * (1651022837 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1651022837 / 500000000) / 16) (116082381 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3302149917 / 1000000000) : ℝ) / 16) ≤ (2321693 / 1250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3302149917 / 1000000000) / 16) (2321693 / 1250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((797 / 32000) : ℝ) (319 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1651022837 / 500000000) (3302149917 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (797 / 32000) (319 / 12800) (1051074001523 / 1000000000000) (10511068481 / 10000000000) (1651022837 / 500000000) (3302149917 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (797 / 32000) (319 / 12800) (1651022837 / 500000000) (3302149917 / 1000000000) (49852109 / 1000000000000) (49867703 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1651022837 / 500000000) (3302149917 / 1000000000) (116082381 / 62500000) (2321693 / 1250000) (49852109 / 1000000000000) (49867703 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0346 :
    ∀ t ∈ Set.Icc ((319 / 12800) : ℝ) (399 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1051106848099 / 1000000000000) : ℝ) ≤ Real.exp (2 * (319 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (319 / 12800)) (1051106848099 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((399 / 16000) : ℝ)) ≤ (525569847851 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (399 / 16000)) (525569847851 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1857354033 / 1000000000) : ℝ) ≤ Real.exp (3 * (660429773 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (660429773 / 200000000) / 16) (1857354033 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3302253111 / 1000000000) : ℝ) / 16) ≤ (928695169 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3302253111 / 1000000000) / 16) (928695169 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((319 / 12800) : ℝ) (399 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (660429773 / 200000000) (3302253111 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (319 / 12800) (399 / 16000) (1051106848099 / 1000000000000) (525569847851 / 500000000000) (660429773 / 200000000) (3302253111 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (319 / 12800) (399 / 16000) (660429773 / 200000000) (3302253111 / 1000000000) (24918339 / 500000000000) (49852267 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (660429773 / 200000000) (3302253111 / 1000000000) (1857354033 / 1000000000) (928695169 / 500000000) (24918339 / 500000000000) (49852267 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0347 :
    ∀ t ∈ Set.Icc ((399 / 16000) : ℝ) (1597 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1051139695701 / 1000000000000) : ℝ) ≤ Real.exp (2 * (399 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (399 / 16000)) (1051139695701 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1597 / 64000) : ℝ)) ≤ (1051172544331 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1597 / 64000)) (1051172544331 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1857389971 / 1000000000) : ℝ) ≤ Real.exp (3 * (1651126029 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1651126029 / 500000000) / 16) (1857389971 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((825589077 / 250000000) : ℝ) / 16) ≤ (928713139 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (825589077 / 250000000) / 16) (928713139 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((399 / 16000) : ℝ) (1597 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1651126029 / 500000000) (825589077 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (399 / 16000) (1597 / 64000) (1051139695701 / 1000000000000) (1051172544331 / 1000000000000) (1651126029 / 500000000) (825589077 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (399 / 16000) (1597 / 64000) (1651126029 / 500000000) (825589077 / 250000000) (49821251 / 1000000000000) (12459209 / 250000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1651126029 / 500000000) (825589077 / 250000000) (1857389971 / 1000000000) (928713139 / 500000000) (49821251 / 1000000000000) (12459209 / 250000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0348 :
    ∀ t ∈ Set.Icc ((1597 / 64000) : ℝ) (799 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((105117254433 / 100000000000) : ℝ) ≤ Real.exp (2 * (1597 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1597 / 64000)) (105117254433 / 100000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((799 / 32000) : ℝ)) ≤ (525602696993 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (799 / 32000)) (525602696993 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((185742591 / 100000000) : ℝ) ≤ Real.exp (3 * (660471051 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (660471051 / 200000000) / 16) (185742591 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((825614877 / 250000000) : ℝ) / 16) ≤ (92873111 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (825614877 / 250000000) / 16) (92873111 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1597 / 64000) : ℝ) (799 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (660471051 / 200000000) (825614877 / 250000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1597 / 64000) (799 / 32000) (105117254433 / 100000000000) (525602696993 / 500000000000) (660471051 / 200000000) (825614877 / 250000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1597 / 64000) (799 / 32000) (660471051 / 200000000) (825614877 / 250000000) (49805829 / 1000000000000) (4982141 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (660471051 / 200000000) (825614877 / 250000000) (185742591 / 100000000) (92873111 / 50000000) (49805829 / 1000000000000) (4982141 / 100000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0349 :
    ∀ t ∈ Set.Icc ((799 / 32000) : ℝ) (1599 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((210241078797 / 200000000000) : ℝ) ≤ Real.exp (2 * (799 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (799 / 32000)) (210241078797 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1599 / 64000) : ℝ)) ≤ (262809561167 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1599 / 64000)) (262809561167 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((464365463 / 250000000) : ℝ) ≤ Real.exp (3 * (412807307 / 125000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (412807307 / 125000000) / 16) (464365463 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3302562711 / 1000000000) : ℝ) / 16) ≤ (1857498163 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3302562711 / 1000000000) / 16) (1857498163 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((799 / 32000) : ℝ) (1599 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (412807307 / 125000000) (3302562711 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (799 / 32000) (1599 / 64000) (210241078797 / 200000000000) (262809561167 / 250000000000) (412807307 / 125000000) (3302562711 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (799 / 32000) (1599 / 64000) (412807307 / 125000000) (3302562711 / 1000000000) (49790411 / 1000000000000) (49805987 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (412807307 / 125000000) (3302562711 / 1000000000) (464365463 / 250000000) (1857498163 / 1000000000) (49790411 / 1000000000000) (49805987 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0350 :
    ∀ t ∈ Set.Icc ((1599 / 64000) : ℝ) (1 / 40), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1051238244667 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1599 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1599 / 64000)) (1051238244667 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1 / 40) : ℝ)) ≤ (1051271096377 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1 / 40)) (1051271096377 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((371499559 / 200000000) : ℝ) ≤ Real.exp (3 * (3302561659 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3302561659 / 1000000000) / 16) (371499559 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1651332959 / 500000000) : ℝ) / 16) ≤ (464383527 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1651332959 / 500000000) / 16) (464383527 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1599 / 64000) : ℝ) (1 / 40),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3302561659 / 1000000000) (1651332959 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1599 / 64000) (1 / 40) (1051238244667 / 1000000000000) (1051271096377 / 1000000000000) (3302561659 / 1000000000) (1651332959 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1599 / 64000) (1 / 40) (3302561659 / 1000000000) (1651332959 / 500000000) (49774997 / 1000000000000) (4979057 / 100000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3302561659 / 1000000000) (1651332959 / 500000000) (371499559 / 200000000) (464383527 / 250000000) (49774997 / 1000000000000) (4979057 / 100000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0351 :
    ∀ t ∈ Set.Icc ((1 / 40) : ℝ) (1601 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((131408887047 / 125000000000) : ℝ) ≤ Real.exp (2 * (1 / 40)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1 / 40)) (131408887047 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1601 / 64000) : ℝ)) ≤ (131412993639 / 125000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1601 / 64000)) (131412993639 / 125000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1857533741 / 1000000000) : ℝ) ≤ Real.exp (3 * (1651332433 / 500000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1651332433 / 500000000) / 16) (1857533741 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((412846141 / 125000000) : ℝ) / 16) ≤ (371514011 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (412846141 / 125000000) / 16) (371514011 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1 / 40) : ℝ) (1601 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1651332433 / 500000000) (412846141 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1 / 40) (1601 / 64000) (131408887047 / 125000000000) (131412993639 / 125000000000) (1651332433 / 500000000) (412846141 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1 / 40) (1601 / 64000) (1651332433 / 500000000) (412846141 / 125000000) (12439897 / 250000000000) (9955031 / 200000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (1651332433 / 500000000) (412846141 / 125000000) (1857533741 / 1000000000) (371514011 / 200000000) (12439897 / 250000000000) (9955031 / 200000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0352 :
    ∀ t ∈ Set.Icc ((1601 / 64000) : ℝ) (801 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1051303949111 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1601 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1601 / 64000)) (1051303949111 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((801 / 32000) : ℝ)) ≤ (1051336802873 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (801 / 32000)) (1051336802873 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((232196211 / 125000000) : ℝ) ≤ Real.exp (3 * (825692019 / 250000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (825692019 / 250000000) / 16) (232196211 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3302872341 / 1000000000) : ℝ) / 16) ≤ (464401501 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3302872341 / 1000000000) / 16) (464401501 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1601 / 64000) : ℝ) (801 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (825692019 / 250000000) (3302872341 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1601 / 64000) (801 / 32000) (1051303949111 / 1000000000000) (1051336802873 / 1000000000000) (825692019 / 250000000) (3302872341 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1601 / 64000) (801 / 32000) (825692019 / 250000000) (3302872341 / 1000000000) (49744183 / 1000000000000) (24879873 / 500000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (825692019 / 250000000) (3302872341 / 1000000000) (232196211 / 125000000) (464401501 / 250000000) (49744183 / 1000000000000) (24879873 / 500000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0353 :
    ∀ t ∈ Set.Icc ((801 / 32000) : ℝ) (1603 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((131417100359 / 125000000000) : ℝ) ≤ Real.exp (2 * (801 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (801 / 32000)) (131417100359 / 125000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1603 / 64000) : ℝ)) ≤ (525684828831 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1603 / 64000)) (525684828831 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1857605637 / 1000000000) : ℝ) ≤ Real.exp (3 * (3302871289 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3302871289 / 1000000000) / 16) (1857605637 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3302975557 / 1000000000) : ℝ) / 16) ≤ (371528391 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3302975557 / 1000000000) / 16) (371528391 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((801 / 32000) : ℝ) (1603 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3302871289 / 1000000000) (3302975557 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (801 / 32000) (1603 / 64000) (131417100359 / 125000000000) (525684828831 / 500000000000) (3302871289 / 1000000000) (3302975557 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (801 / 32000) (1603 / 64000) (3302871289 / 1000000000) (3302975557 / 1000000000) (24864391 / 500000000000) (49744341 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3302871289 / 1000000000) (3302975557 / 1000000000) (1857605637 / 1000000000) (371528391 / 200000000) (24864391 / 500000000000) (49744341 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0354 :
    ∀ t ∈ Set.Icc ((1603 / 64000) : ℝ) (401 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1051369657661 / 1000000000000) : ℝ) ≤ Real.exp (2 * (1603 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1603 / 64000)) (1051369657661 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((401 / 16000) : ℝ)) ≤ (1051402513477 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (401 / 16000)) (1051402513477 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1857641587 / 1000000000) : ℝ) ≤ Real.exp (3 * (660594901 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (660594901 / 200000000) / 16) (1857641587 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3303078777 / 1000000000) : ℝ) / 16) ≤ (464419477 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3303078777 / 1000000000) / 16) (464419477 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1603 / 64000) : ℝ) (401 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (660594901 / 200000000) (3303078777 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1603 / 64000) (401 / 16000) (1051369657661 / 1000000000000) (1051402513477 / 1000000000000) (660594901 / 200000000) (3303078777 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1603 / 64000) (401 / 16000) (660594901 / 200000000) (3303078777 / 1000000000) (9942677 / 200000000000) (2486447 / 50000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (660594901 / 200000000) (3303078777 / 1000000000) (1857641587 / 1000000000) (464419477 / 250000000) (9942677 / 200000000000) (2486447 / 50000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0355 :
    ∀ t ∈ Set.Icc ((401 / 16000) : ℝ) (321 / 12800), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((262850628369 / 250000000000) : ℝ) ≤ Real.exp (2 * (401 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (401 / 16000)) (262850628369 / 250000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((321 / 12800) : ℝ)) ≤ (1051435370319 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (321 / 12800)) (1051435370319 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((92883877 / 50000000) : ℝ) ≤ Real.exp (3 * (132123109 / 40000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (132123109 / 40000000) / 16) (92883877 / 50000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1651591 / 500000) : ℝ) / 16) ≤ (928856931 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1651591 / 500000) / 16) (928856931 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((401 / 16000) : ℝ) (321 / 12800),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (132123109 / 40000000) (1651591 / 500000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (401 / 16000) (321 / 12800) (262850628369 / 250000000000) (1051435370319 / 1000000000000) (132123109 / 40000000) (1651591 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (401 / 16000) (321 / 12800) (132123109 / 40000000) (1651591 / 500000) (49697993 / 1000000000000) (49713543 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (132123109 / 40000000) (1651591 / 500000) (92883877 / 50000000) (928856931 / 500000000) (49697993 / 1000000000000) (49713543 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0356 :
    ∀ t ∈ Set.Icc ((321 / 12800) : ℝ) (803 / 32000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((525717685159 / 500000000000) : ℝ) ≤ Real.exp (2 * (321 / 12800)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (321 / 12800)) (525717685159 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((803 / 32000) : ℝ)) ≤ (262867057047 / 250000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (803 / 32000)) (262867057047 / 250000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((928856747 / 500000000) : ℝ) ≤ Real.exp (3 * (3303180947 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3303180947 / 1000000000) / 16) (928856747 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((1651642613 / 500000000) : ℝ) / 16) ≤ (928874909 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (1651642613 / 500000000) / 16) (928874909 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((321 / 12800) : ℝ) (803 / 32000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3303180947 / 1000000000) (1651642613 / 500000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (321 / 12800) (803 / 32000) (525717685159 / 500000000000) (262867057047 / 250000000000) (3303180947 / 1000000000) (1651642613 / 500000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (321 / 12800) (803 / 32000) (3303180947 / 1000000000) (1651642613 / 500000000) (9936521 / 200000000000) (49698151 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3303180947 / 1000000000) (1651642613 / 500000000) (928856747 / 500000000) (928874909 / 500000000) (9936521 / 200000000000) (49698151 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0357 :
    ∀ t ∈ Set.Icc ((803 / 32000) : ℝ) (1607 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1051468228187 / 1000000000000) : ℝ) ≤ Real.exp (2 * (803 / 32000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (803 / 32000)) (1051468228187 / 1000000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1607 / 64000) : ℝ)) ≤ (1051501087083 / 1000000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1607 / 64000)) (1051501087083 / 1000000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((37154989 / 20000000) : ℝ) ≤ Real.exp (3 * (3303284173 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3303284173 / 1000000000) / 16) (37154989 / 20000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((660677691 / 200000000) : ℝ) / 16) ≤ (116111611 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (660677691 / 200000000) / 16) (116111611 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((803 / 32000) : ℝ) (1607 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3303284173 / 1000000000) (660677691 / 200000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (803 / 32000) (1607 / 64000) (1051468228187 / 1000000000000) (1051501087083 / 1000000000000) (3303284173 / 1000000000) (660677691 / 200000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (803 / 32000) (1607 / 64000) (3303284173 / 1000000000) (660677691 / 200000000) (49667221 / 1000000000000) (49682763 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3303284173 / 1000000000) (660677691 / 200000000) (37154989 / 20000000) (116111611 / 62500000) (49667221 / 1000000000000) (49682763 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0358 :
    ∀ t ∈ Set.Icc ((1607 / 64000) : ℝ) (201 / 8000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((525750543541 / 500000000000) : ℝ) ≤ Real.exp (2 * (1607 / 64000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1607 / 64000)) (525750543541 / 500000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((201 / 8000) : ℝ)) ≤ (525766973503 / 500000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (201 / 8000)) (525766973503 / 500000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((1857785409 / 1000000000) : ℝ) ≤ Real.exp (3 * (3303387403 / 1000000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3303387403 / 1000000000) / 16) (1857785409 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((412936461 / 125000000) : ℝ) / 16) ≤ (232227717 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (412936461 / 125000000) / 16) (232227717 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1607 / 64000) : ℝ) (201 / 8000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3303387403 / 1000000000) (412936461 / 125000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (1607 / 64000) (201 / 8000) (525750543541 / 500000000000) (525766973503 / 500000000000) (3303387403 / 1000000000) (412936461 / 125000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (1607 / 64000) (201 / 8000) (3303387403 / 1000000000) (412936461 / 125000000) (24825921 / 500000000000) (49667379 / 1000000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (3303387403 / 1000000000) (412936461 / 125000000) (1857785409 / 1000000000) (232227717 / 125000000) (24825921 / 500000000000) (49667379 / 1000000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

set_option maxHeartbeats 2000000 in
theorem hpThetaDensityTwoTermCompact_cell0359 :
    ∀ t ∈ Set.Icc ((201 / 8000) : ℝ) (1609 / 64000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((210306789401 / 200000000000) : ℝ) ≤ Real.exp (2 * (201 / 8000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (201 / 8000)) (210306789401 / 200000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1609 / 64000) : ℝ)) ≤ (210313361591 / 200000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1609 / 64000)) (210313361591 / 200000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hvL : ((232227671 / 125000000) : ℝ) ≤ Real.exp (3 * (660698127 / 200000000) / 16) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (660698127 / 200000000) / 16) (232227671 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hvU : Real.exp (3 * ((3303594923 / 1000000000) : ℝ) / 16) ≤ (1857857697 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (3 * (3303594923 / 1000000000) / 16) (1857857697 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((201 / 8000) : ℝ) (1609 / 64000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (660698127 / 200000000) (3303594923 / 1000000000) := by
    intro t ht
    exact hpThetaDensityTwoTerm_parameter_bounds
      (201 / 8000) (1609 / 64000) (210306789401 / 200000000000) (210313361591 / 200000000000) (660698127 / 200000000) (3303594923 / 1000000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityTwoTerm_interval_certificate
    (201 / 8000) (1609 / 64000) (660698127 / 200000000) (3303594923 / 1000000000) (49636467 / 1000000000000) (12413 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityTwoTerm_exponential_bounds
      (660698127 / 200000000) (3303594923 / 1000000000) (232227671 / 125000000) (1857857697 / 1000000000) (49636467 / 1000000000000) (12413 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht)
      (by norm_num) (by norm_num) hvL hvU (by norm_num) (by norm_num)
  · norm_num [hpThetaDensityTwoTermCellMargin, hpThetaDensityCurvatureBoxMargin,
      hpThetaDensityTwoTermP, hpThetaDensityTwoTermD, hpThetaDensityTwoTermQ]

theorem hpThetaDensityTwoTermCompact_cellsBatch017 :
    ∀ t ∈ Set.Icc ((1589 / 64000) : ℝ) (1609 / 64000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0340
      hpThetaDensityTwoTermCompact_cell0341)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0342
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0343
      hpThetaDensityTwoTermCompact_cell0344)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0345
      hpThetaDensityTwoTermCompact_cell0346)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0347
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0348
      hpThetaDensityTwoTermCompact_cell0349))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0350
      hpThetaDensityTwoTermCompact_cell0351)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0352
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0353
      hpThetaDensityTwoTermCompact_cell0354)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0355
      hpThetaDensityTwoTermCompact_cell0356)
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0357
      (hpThetaDensityCells_positive_glue hpThetaDensityTwoTermCompact_cell0358
      hpThetaDensityTwoTermCompact_cell0359)))))

#print axioms hpThetaDensityTwoTermCompact_cellsBatch017
end HodgeProofHP
