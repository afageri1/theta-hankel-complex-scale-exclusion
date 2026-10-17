/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityCurvatureRationalCells

/-! Exact rational certificates with a full infinite-series remainder bound. -/
noncomputable section
namespace HodgeProofHP

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell120 :
    ∀ t ∈ Set.Icc ((73 / 400) : ℝ) (183 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((180064251 / 125000000) : ℝ) ≤ Real.exp (2 * (73 / 400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (73 / 400)) (180064251 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((183 / 1000) : ℝ)) ≤ (1441955243 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (183 / 1000)) (1441955243 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((393548841249 / 500000) : ℝ) ≤ Real.exp (3 * (2262687 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2262687 / 500000)) (393548841249 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((73 / 400) : ℝ) (183 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2262687 / 500000) (4530047 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (73 / 400) (183 / 1000) (180064251 / 125000000) (1441955243 / 1000000000) (2262687 / 500000) (4530047 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (73 / 400) (183 / 1000) (2262687 / 500000) (4530047 / 1000000) (10947 / 200) (27467 / 500)
    (96821 / 500) (197281 / 1000) (-85061 / 200) (119 / 40) (3368999 / 500) (162623 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2262687 / 500000) (393548841249 / 500000) (162623 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2262687 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2262687 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell121 :
    ∀ t ∈ Set.Icc ((183 / 1000) : ℝ) (367 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((720977621 / 500000000) : ℝ) ≤ Real.exp (2 * (183 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (183 / 1000)) (720977621 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((367 / 2000) : ℝ)) ≤ (9021237 / 6250000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (367 / 2000)) (9021237 / 6250000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((797862346311 / 1000000) : ℝ) ≤ Real.exp (3 * (2264951 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2264951 / 500000)) (797862346311 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((183 / 1000) : ℝ) (367 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2264951 / 500000) (4534579 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (183 / 1000) (367 / 2000) (720977621 / 500000000) (9021237 / 6250000) (2264951 / 500000) (4534579 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (183 / 1000) (367 / 2000) (2264951 / 500000) (4534579 / 1000000) (6859 / 125) (55071 / 1000)
    (38941 / 200) (99177 / 500) (-422881 / 1000) (373 / 125) (3382501 / 500) (160429 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2264951 / 500000) (797862346311 / 1000000) (160429 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2264951 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2264951 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell122 :
    ∀ t ∈ Set.Icc ((367 / 2000) : ℝ) (23 / 125), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1443397919 / 1000000000) : ℝ) ≤ Real.exp (2 * (367 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (367 / 2000)) (1443397919 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((23 / 125) : ℝ)) ≤ (1444842039 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (23 / 125)) (1444842039 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((404391966603 / 500000) : ℝ) ≤ Real.exp (3 * (2267217 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2267217 / 500000)) (404391966603 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((367 / 2000) : ℝ) (23 / 125),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2267217 / 500000) (1134779 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (367 / 2000) (23 / 125) (1443397919 / 1000000000) (1444842039 / 1000000000) (2267217 / 500000) (1134779 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (367 / 2000) (23 / 125) (2267217 / 500000) (1134779 / 250000) (55009 / 1000) (6901 / 125)
    (48943 / 250) (199431 / 1000) (-420421 / 1000) (2993 / 1000) (6792117 / 1000) (12661 / 40000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2267217 / 500000) (404391966603 / 500000) (12661 / 40000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2267217 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2267217 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell123 :
    ∀ t ∈ Set.Icc ((23 / 125) : ℝ) (369 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((722421019 / 500000000) : ℝ) ≤ Real.exp (2 * (23 / 125)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (23 / 125)) (722421019 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((369 / 2000) : ℝ)) ≤ (361571901 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (369 / 2000)) (361571901 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((204966828627 / 250000) : ℝ) ≤ Real.exp (3 * (4538971 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4538971 / 1000000)) (204966828627 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((23 / 125) : ℝ) (369 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4538971 / 1000000) (2271829 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (23 / 125) (369 / 2000) (722421019 / 500000000) (361571901 / 250000000) (4538971 / 1000000) (2271829 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (23 / 125) (369 / 2000) (4538971 / 1000000) (2271829 / 500000) (55147 / 1000) (27673 / 500)
    (49211 / 250) (25064 / 125) (-417933 / 1000) (1501 / 500) (6819343 / 1000) (156123 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4538971 / 1000000) (204966828627 / 250000) (156123 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4538971 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4538971 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell124 :
    ∀ t ∈ Set.Icc ((369 / 2000) : ℝ) (37 / 200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1446287603 / 1000000000) : ℝ) ≤ Real.exp (2 * (369 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (369 / 2000)) (1446287603 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((37 / 200) : ℝ)) ≤ (289546923 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (37 / 200)) (289546923 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((207778137177 / 250000) : ℝ) ≤ Real.exp (3 * (567939 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (567939 / 125000)) (207778137177 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((369 / 2000) : ℝ) (37 / 200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (567939 / 125000) (1137051 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (369 / 2000) (37 / 200) (1446287603 / 1000000000) (289546923 / 200000000) (567939 / 125000) (1137051 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (369 / 2000) (37 / 200) (567939 / 125000) (1137051 / 250000) (13821 / 250) (13871 / 250)
    (197919 / 1000) (100799 / 500) (-415417 / 1000) (3011 / 1000) (1711669 / 250) (308021 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (567939 / 125000) (207778137177 / 250000) (308021 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (567939 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (567939 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell125 :
    ∀ t ∈ Set.Icc ((37 / 200) : ℝ) (371 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((723867307 / 500000000) : ℝ) ≤ Real.exp (2 * (37 / 200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (37 / 200)) (723867307 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((371 / 2000) : ℝ)) ≤ (724591537 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (371 / 2000)) (724591537 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((842524654821 / 1000000) : ℝ) ≤ Real.exp (3 * (2274029 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2274029 / 500000)) (842524654821 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((37 / 200) : ℝ) (371 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2274029 / 500000) (2276377 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (37 / 200) (371 / 2000) (723867307 / 500000000) (724591537 / 500000000) (2274029 / 500000) (2276377 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (37 / 200) (371 / 2000) (2274029 / 500000) (2276377 / 500000) (27711 / 500) (27811 / 500)
    199 (202687 / 1000) (-10322 / 25) (151 / 50) (3437057 / 500) (303849 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2274029 / 500000) (842524654821 / 1000000) (303849 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2274029 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2274029 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell126 :
    ∀ t ∈ Set.Icc ((371 / 2000) : ℝ) (93 / 500), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1449183073 / 1000000000) : ℝ) ≤ Real.exp (2 * (371 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (371 / 2000)) (1449183073 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((93 / 500) : ℝ)) ≤ (725316491 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (93 / 500)) (725316491 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((854103706437 / 1000000) : ℝ) ≤ Real.exp (3 * (142269 / 31250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (142269 / 31250)) (854103706437 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((371 / 2000) : ℝ) (93 / 500),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (142269 / 31250) (4557309 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (371 / 2000) (93 / 500) (1449183073 / 1000000000) (725316491 / 500000000) (142269 / 31250) (4557309 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (371 / 2000) (93 / 500) (142269 / 31250) (4557309 / 1000000) (55561 / 1000) (55761 / 1000)
    (50021 / 250) (203781 / 1000) (-410307 / 1000) (3029 / 1000) (3450833 / 500) (29973 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (142269 / 31250) (854103706437 / 1000000) (29973 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (142269 / 31250)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (142269 / 31250)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell127 :
    ∀ t ∈ Set.Icc ((93 / 500) : ℝ) (373 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1450632981 / 1000000000) : ℝ) ≤ Real.exp (2 * (93 / 500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (93 / 500)) (1450632981 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((373 / 2000) : ℝ)) ≤ (72604217 / 50000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (373 / 2000)) (72604217 / 50000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((865854875033 / 1000000) : ℝ) ≤ Real.exp (3 * (4557163 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4557163 / 1000000)) (865854875033 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((93 / 500) : ℝ) (373 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4557163 / 1000000) (4561869 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (93 / 500) (373 / 2000) (1450632981 / 1000000000) (72604217 / 50000000) (4557163 / 1000000) (4561869 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (93 / 500) (373 / 2000) (4557163 / 1000000) (4561869 / 1000000) (55699 / 1000) (559 / 10)
    (201173 / 1000) (5122 / 25) (-81541 / 200) (1519 / 500) (692933 / 100) (147831 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4557163 / 1000000) (865854875033 / 1000000) (147831 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4557163 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4557163 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell128 :
    ∀ t ∈ Set.Icc ((373 / 2000) : ℝ) (187 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1452084339 / 1000000000) : ℝ) ≤ Real.exp (2 * (373 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (373 / 2000)) (1452084339 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((187 / 1000) : ℝ)) ≤ (1453537151 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (187 / 1000)) (1453537151 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((877778250141 / 1000000) : ℝ) ≤ Real.exp (3 * (2280861 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2280861 / 500000)) (877778250141 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((373 / 2000) : ℝ) (187 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2280861 / 500000) (4566433 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (373 / 2000) (187 / 1000) (1452084339 / 1000000000) (1453537151 / 1000000000) (2280861 / 500000) (4566433 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (373 / 2000) (187 / 1000) (2280861 / 500000) (4566433 / 1000000) (27919 / 500) (56039 / 1000)
    (101133 / 500) (205983 / 1000) (-202537 / 500) (381 / 125) (3478551 / 500) (145823 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2280861 / 500000) (877778250141 / 1000000) (145823 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2280861 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2280861 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell129 :
    ∀ t ∈ Set.Icc ((187 / 1000) : ℝ) (3 / 16), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((29070743 / 20000000) : ℝ) ≤ Real.exp (2 * (187 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (187 / 1000)) (29070743 / 20000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((3 / 16) : ℝ)) ≤ (290998283 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (3 / 16)) (290998283 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((444939580317 / 500000) : ℝ) ≤ Real.exp (3 * (2283143 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2283143 / 500000)) (444939580317 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((187 / 1000) : ℝ) (3 / 16),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2283143 / 500000) (2285501 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (187 / 1000) (3 / 16) (29070743 / 20000000) (290998283 / 200000000) (2283143 / 500000) (2285501 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (187 / 1000) (3 / 16) (2283143 / 500000) (2285501 / 500000) (55977 / 1000) (56179 / 1000)
    (50841 / 250) (207091 / 1000) (-201207 / 500) (3057 / 1000) (1746247 / 250) (899 / 3125000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2283143 / 500000) (444939580317 / 500000) (899 / 3125000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2283143 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2283143 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell130 :
    ∀ t ∈ Set.Icc ((3 / 16) : ℝ) (47 / 250), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((727495707 / 500000000) : ℝ) ≤ Real.exp (2 * (3 / 16)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (3 / 16)) (727495707 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((47 / 250) : ℝ)) ≤ (728223567 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (47 / 250)) (728223567 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((902160419281 / 1000000) : ℝ) ≤ Real.exp (3 * (914171 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (914171 / 200000)) (902160419281 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((3 / 16) : ℝ) (47 / 250),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (914171 / 200000) (183023 / 40000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (3 / 16) (47 / 250) (727495707 / 500000000) (728223567 / 500000000) (914171 / 200000) (183023 / 40000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (3 / 16) (47 / 250) (914171 / 200000) (183023 / 40000) (56117 / 1000) (56319 / 1000)
    (102233 / 500) (104101 / 500) (-99933 / 250) (1533 / 500) (3506491 / 500) (70941 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (914171 / 200000) (902160419281 / 1000000) (70941 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (914171 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (914171 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell131 :
    ∀ t ∈ Set.Icc ((47 / 250) : ℝ) (377 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1456447133 / 1000000000) : ℝ) ≤ Real.exp (2 * (47 / 250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (47 / 250)) (1456447133 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((377 / 2000) : ℝ)) ≤ (145790431 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (377 / 2000)) (145790431 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((914622142011 / 1000000) : ℝ) ≤ Real.exp (3 * (1143857 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1143857 / 250000)) (914622142011 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((47 / 250) : ℝ) (377 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1143857 / 250000) (4580153 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (47 / 250) (377 / 2000) (1456447133 / 1000000000) (145790431 / 100000000) (1143857 / 250000) (4580153 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (47 / 250) (377 / 2000) (1143857 / 250000) (4580153 / 1000000) (56257 / 1000) (56459 / 1000)
    (205573 / 1000) (209319 / 1000) (-397013 / 1000) (123 / 40) (7041091 / 1000) (139949 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1143857 / 250000) (914622142011 / 1000000) (139949 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1143857 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1143857 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell132 :
    ∀ t ∈ Set.Icc ((377 / 2000) : ℝ) (189 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1457904309 / 1000000000) : ℝ) ≤ Real.exp (2 * (377 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (377 / 2000)) (1457904309 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((189 / 1000) : ℝ)) ≤ (1459362943 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (189 / 1000)) (1459362943 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((927269904249 / 1000000) : ℝ) ≤ Real.exp (3 * (2290003 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2290003 / 500000)) (927269904249 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((377 / 2000) : ℝ) (189 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2290003 / 500000) (916947 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (377 / 2000) (189 / 1000) (1457904309 / 1000000000) (1459362943 / 1000000000) (2290003 / 500000) (916947 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (377 / 2000) (189 / 1000) (2290003 / 500000) (916947 / 200000) (56397 / 1000) (283 / 5)
    (51671 / 250) (210439 / 1000) (-394271 / 1000) (771 / 250) (7069309 / 1000) (3451 / 12500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2290003 / 500000) (927269904249 / 1000000) (3451 / 12500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2290003 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2290003 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell133 :
    ∀ t ∈ Set.Icc ((189 / 1000) : ℝ) (379 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((729681471 / 500000000) : ℝ) ≤ Real.exp (2 * (189 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (189 / 1000)) (729681471 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((379 / 2000) : ℝ)) ≤ (365205759 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (379 / 2000)) (365205759 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((940103840179 / 1000000) : ℝ) ≤ Real.exp (3 * (1146147 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1146147 / 250000)) (940103840179 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((189 / 1000) : ℝ) (379 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1146147 / 250000) (2294661 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (189 / 1000) (379 / 2000) (729681471 / 500000000) (365205759 / 250000000) (1146147 / 250000) (2294661 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (189 / 1000) (379 / 2000) (1146147 / 250000) (2294661 / 500000) (56537 / 1000) (2837 / 50)
    (207799 / 1000) (42313 / 200) (-391493 / 1000) (1547 / 500) (7097643 / 1000) (272311 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1146147 / 250000) (940103840179 / 1000000) (272311 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1146147 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1146147 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell134 :
    ∀ t ∈ Set.Icc ((379 / 2000) : ℝ) (19 / 100), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((292164607 / 200000000) : ℝ) ≤ Real.exp (2 * (379 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (379 / 2000)) (292164607 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((19 / 100) : ℝ)) ≤ (146228459 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (19 / 100)) (146228459 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((476564847873 / 500000) : ℝ) ≤ Real.exp (3 * (183567 / 40000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (183567 / 40000)) (476564847873 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((379 / 2000) : ℝ) (19 / 100),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (183567 / 40000) (2296957 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (379 / 2000) (19 / 100) (292164607 / 200000000) (146228459 / 100000000) (183567 / 40000) (2296957 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (379 / 2000) (19 / 100) (183567 / 40000) (2296957 / 500000) (28339 / 500) (28441 / 500)
    (208919 / 1000) (42539 / 200) (-97171 / 250) (3103 / 1000) (7126093 / 1000) (268589 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (183567 / 40000) (476564847873 / 500000) (268589 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (183567 / 40000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (183567 / 40000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell135 :
    ∀ t ∈ Set.Icc ((19 / 100) : ℝ) (381 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1462284589 / 1000000000) : ℝ) ≤ Real.exp (2 * (19 / 100)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (19 / 100)) (1462284589 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((381 / 2000) : ℝ)) ≤ (731873803 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (381 / 2000)) (731873803 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((966350523351 / 1000000) : ℝ) ≤ Real.exp (3 * (4593767 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4593767 / 1000000)) (966350523351 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((19 / 100) : ℝ) (381 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4593767 / 1000000) (459851 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (19 / 100) (381 / 2000) (1462284589 / 1000000000) (731873803 / 500000000) (4593767 / 1000000) (459851 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (19 / 100) (381 / 2000) (4593767 / 1000000) (459851 / 100000) (56819 / 1000) (57023 / 1000)
    (52511 / 250) (213829 / 1000) (-96463 / 250) (389 / 125) (7154653 / 1000) (52983 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4593767 / 1000000) (966350523351 / 1000000) (52983 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4593767 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4593767 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell136 :
    ∀ t ∈ Set.Icc ((381 / 2000) : ℝ) (191 / 1000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((292749521 / 200000000) : ℝ) ≤ Real.exp (2 * (381 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (381 / 2000)) (292749521 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((191 / 1000) : ℝ)) ≤ (732606043 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (191 / 1000)) (732606043 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((979766487313 / 1000000) : ℝ) ≤ Real.exp (3 * (4598363 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4598363 / 1000000)) (979766487313 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((381 / 2000) : ℝ) (191 / 1000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4598363 / 1000000) (4603111 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (381 / 2000) (191 / 1000) (292749521 / 200000000) (732606043 / 500000000) (4598363 / 1000000) (4603111 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (381 / 2000) (191 / 1000) (4598363 / 1000000) (4603111 / 1000000) (56961 / 1000) (11433 / 200)
    (211173 / 1000) (26871 / 125) (-191491 / 500) (1561 / 500) (718333 / 100) (261287 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4598363 / 1000000) (979766487313 / 1000000) (261287 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4598363 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4598363 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell137 :
    ∀ t ∈ Set.Icc ((191 / 1000) : ℝ) (383 / 2000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((293042417 / 200000000) : ℝ) ≤ Real.exp (2 * (191 / 1000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (191 / 1000)) (293042417 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((383 / 2000) : ℝ)) ≤ (1466678031 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (383 / 2000)) (1466678031 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((198676124133 / 200000) : ℝ) ≤ Real.exp (3 * (4602963 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4602963 / 1000000)) (198676124133 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((191 / 1000) : ℝ) (383 / 2000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4602963 / 1000000) (1151929 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (191 / 1000) (383 / 2000) (293042417 / 200000000) (1466678031 / 1000000000) (4602963 / 1000000) (1151929 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (191 / 1000) (383 / 2000) (4602963 / 1000000) (1151929 / 250000) (28551 / 500) (57307 / 1000)
    (106153 / 500) (216111 / 1000) (-190041 / 500) (3131 / 1000) (3606059 / 500) (128853 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4602963 / 1000000) (198676124133 / 200000) (128853 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4602963 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4602963 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell138 :
    ∀ t ∈ Set.Icc ((383 / 2000) : ℝ) (24 / 125), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((146667803 / 100000000) : ℝ) ≤ Real.exp (2 * (383 / 2000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (383 / 2000)) (146667803 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((24 / 125) : ℝ)) ≤ (734072721 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (24 / 125)) (734072721 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((15737532012 / 15625) : ℝ) ≤ Real.exp (3 * (4607569 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (4607569 / 1000000)) (15737532012 / 15625) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((383 / 2000) : ℝ) (24 / 125),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (4607569 / 1000000) (2306163 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (383 / 2000) (24 / 125) (146667803 / 100000000) (734072721 / 500000000) (4607569 / 1000000) (2306163 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (383 / 2000) (24 / 125) (4607569 / 1000000) (2306163 / 500000) (14311 / 250) (57449 / 1000)
    (42689 / 200) (217259 / 1000) (-188579 / 500) (157 / 50) (905128 / 125) (25417 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (4607569 / 1000000) (15737532012 / 15625) (25417 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4607569 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (4607569 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityCompact_cell139 :
    ∀ t ∈ Set.Icc ((24 / 125) : ℝ) (77 / 400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1468145441 / 1000000000) : ℝ) ≤ Real.exp (2 * (24 / 125)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (24 / 125)) (1468145441 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((77 / 400) : ℝ)) ≤ (734807161 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (77 / 400)) (734807161 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((1021224965733 / 1000000) : ℝ) ≤ Real.exp (3 * (2306089 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (2306089 / 500000)) (1021224965733 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((24 / 125) : ℝ) (77 / 400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (2306089 / 500000) (4616941 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (24 / 125) (77 / 400) (1468145441 / 1000000000) (734807161 / 500000000) (2306089 / 500000) (4616941 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityCells_interval_certificate
    (24 / 125) (77 / 400) (2306089 / 500000) (4616941 / 1000000) (57387 / 1000) (7199 / 125)
    (214587 / 1000) (54603 / 250) (-93547 / 250) (63 / 20) (7270049 / 1000) (6267 / 25000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (2306089 / 500000) (1021224965733 / 1000000) (6267 / 25000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2306089 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2306089 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityCompact_cellsBatch006 :
    ∀ t ∈ Set.Icc ((73 / 400) : ℝ) (77 / 400),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell120
      hpThetaDensityCompact_cell121)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell122
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell123
      hpThetaDensityCompact_cell124)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell125
      hpThetaDensityCompact_cell126)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell127
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell128
      hpThetaDensityCompact_cell129))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell130
      hpThetaDensityCompact_cell131)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell132
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell133
      hpThetaDensityCompact_cell134)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell135
      hpThetaDensityCompact_cell136)
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell137
      (hpThetaDensityCells_positive_glue hpThetaDensityCompact_cell138
      hpThetaDensityCompact_cell139)))))

#print axioms hpThetaDensityCompact_cellsBatch006
end HodgeProofHP
