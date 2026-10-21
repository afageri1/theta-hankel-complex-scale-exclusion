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
theorem hpThetaDensityExpCompact_cell120 :
    ∀ t ∈ Set.Icc ((1821 / 16000) : ℝ) (1823 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1255614381 / 1000000000) : ℝ) ≤ Real.exp (2 * (1821 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1821 / 16000)) (1255614381 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1823 / 16000) : ℝ)) ≤ (50237133 / 40000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1823 / 16000)) (50237133 / 40000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((34449188037 / 250000) : ℝ) ≤ Real.exp (3 * (61633 / 15625)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (61633 / 15625)) (34449188037 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1821 / 16000) : ℝ) (1823 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (61633 / 15625) (6313 / 1600) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1821 / 16000) (1823 / 16000) (1255614381 / 1000000000) (50237133 / 40000000) (61633 / 15625) (6313 / 1600) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1821 / 16000) (1823 / 16000) (61633 / 15625) (6313 / 1600) (19281 / 500) (7721 / 200)
    (16623 / 200) (20953 / 250) (-575241 / 1000) (114573 / 500000) (3877781 / 1000) (1857809 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (61633 / 15625) (34449188037 / 250000) (1857809 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (61633 / 15625)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (61633 / 15625)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell121 :
    ∀ t ∈ Set.Icc ((1823 / 16000) : ℝ) (73 / 640), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((313982081 / 250000000) : ℝ) ≤ Real.exp (2 * (1823 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1823 / 16000)) (313982081 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((73 / 640) : ℝ)) ≤ (628121173 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (73 / 640)) (628121173 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((8637809857 / 62500) : ℝ) ≤ Real.exp (3 * (1972749 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1972749 / 500000)) (8637809857 / 62500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1823 / 16000) : ℝ) (73 / 640),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1972749 / 500000) (3946611 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1823 / 16000) (73 / 640) (313982081 / 250000000) (628121173 / 500000000) (1972749 / 500000) (3946611 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1823 / 16000) (73 / 640) (1972749 / 500000) (3946611 / 1000000) (9647 / 250) (3863 / 100)
    (16653 / 200) (41981 / 500) (-71909 / 125) (228641 / 1000000) (3881659 / 1000) (926161 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1972749 / 500000) (8637809857 / 62500) (926161 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1972749 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1972749 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell122 :
    ∀ t ∈ Set.Icc ((73 / 640) : ℝ) (1827 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((251248469 / 200000000) : ℝ) ≤ Real.exp (2 * (73 / 640)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (73 / 640)) (251248469 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1827 / 16000) : ℝ)) ≤ (628278223 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1827 / 16000)) (628278223 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((69307394187 / 500000) : ℝ) ≤ Real.exp (3 * (789297 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (789297 / 200000)) (69307394187 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((73 / 640) : ℝ) (1827 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (789297 / 200000) (1973799 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (73 / 640) (1827 / 16000) (251248469 / 200000000) (628278223 / 500000000) (789297 / 200000) (1973799 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (73 / 640) (1827 / 16000) (789297 / 200000) (1973799 / 500000) (38613 / 1000) (4832 / 125)
    (16683 / 200) (10514 / 125) (-575303 / 1000) (28517 / 125000) (3885543 / 1000) (369369 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (789297 / 200000) (69307394187 / 500000) (369369 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (789297 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (789297 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell123 :
    ∀ t ∈ Set.Icc ((1827 / 16000) : ℝ) (1829 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((251311289 / 200000000) : ℝ) ≤ Real.exp (2 * (1827 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1827 / 16000)) (251311289 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1829 / 16000) : ℝ)) ≤ (2010993 / 1600000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1829 / 16000)) (2010993 / 1600000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((139025834337 / 1000000) : ℝ) ≤ Real.exp (3 * (246717 / 62500)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (246717 / 62500)) (139025834337 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1827 / 16000) : ℝ) (1829 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (246717 / 62500) (789717 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1827 / 16000) (1829 / 16000) (251311289 / 200000000) (2010993 / 1600000) (246717 / 62500) (789717 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1827 / 16000) (1829 / 16000) (246717 / 62500) (789717 / 200000) (19319 / 500) (38681 / 1000)
    (16713 / 200) (84263 / 1000) (-575333 / 1000) (14227 / 62500) (388943 / 100) (368277 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (246717 / 62500) (139025834337 / 1000000) (368277 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (246717 / 62500)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (246717 / 62500)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell124 :
    ∀ t ∈ Set.Icc ((1829 / 16000) : ℝ) (1831 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((39277207 / 31250000) : ℝ) ≤ Real.exp (2 * (1829 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1829 / 16000)) (39277207 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1831 / 16000) : ℝ)) ≤ (628592441 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1831 / 16000)) (628592441 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((69719049603 / 500000) : ℝ) ≤ Real.exp (3 * (3948459 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3948459 / 1000000)) (69719049603 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1829 / 16000) : ℝ) (1831 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3948459 / 1000000) (3949573 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1829 / 16000) (1831 / 16000) (39277207 / 31250000) (628592441 / 500000000) (3948459 / 1000000) (3949573 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1829 / 16000) (1831 / 16000) (3948459 / 1000000) (3949573 / 1000000) (38663 / 1000) (19353 / 500)
    (16743 / 200) (84413 / 1000) (-575357 / 1000) (22713 / 100000) (155733 / 40) (1835941 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3948459 / 1000000) (69719049603 / 500000) (1835941 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3948459 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3948459 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell125 :
    ∀ t ∈ Set.Icc ((1831 / 16000) : ℝ) (1833 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1257184881 / 1000000000) : ℝ) ≤ Real.exp (2 * (1831 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1831 / 16000)) (1257184881 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1833 / 16000) : ℝ)) ≤ (1257499217 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1833 / 16000)) (1257499217 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((27970317319 / 200000) : ℝ) ≤ Real.exp (3 * (1974723 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1974723 / 500000)) (27970317319 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1831 / 16000) : ℝ) (1833 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1974723 / 500000) (24691 / 6250) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1831 / 16000) (1833 / 16000) (1257184881 / 1000000000) (1257499217 / 1000000000) (1974723 / 500000) (24691 / 6250) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1831 / 16000) (1833 / 16000) (1974723 / 500000) (24691 / 6250) (38689 / 1000) (9683 / 250)
    (16773 / 200) (21141 / 250) (-287693 / 500) (56657 / 250000) (1948609 / 500) (114407 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1974723 / 500000) (27970317319 / 200000) (114407 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1974723 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1974723 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell126 :
    ∀ t ∈ Set.Icc ((1833 / 16000) : ℝ) (367 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((78593701 / 62500000) : ℝ) ≤ Real.exp (2 * (1833 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1833 / 16000)) (78593701 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((367 / 3200) : ℝ)) ≤ (1257813631 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (367 / 3200)) (1257813631 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((140266300129 / 1000000) : ℝ) ≤ Real.exp (3 * (3950433 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3950433 / 1000000)) (140266300129 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1833 / 16000) : ℝ) (367 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3950433 / 1000000) (987887 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1833 / 16000) (367 / 3200) (78593701 / 62500000) (1257813631 / 1000000000) (3950433 / 1000000) (987887 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1833 / 16000) (367 / 3200) (3950433 / 1000000) (987887 / 250000) (19357 / 500) (38757 / 1000)
    (16803 / 200) (16943 / 200) (-575409 / 1000) (226127 / 1000000) (1950559 / 500) (18251 / 10000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3950433 / 1000000) (140266300129 / 1000000) (18251 / 10000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3950433 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3950433 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell127 :
    ∀ t ∈ Set.Icc ((367 / 3200) : ℝ) (1837 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((125781363 / 100000000) : ℝ) ≤ Real.exp (2 * (367 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (367 / 3200)) (125781363 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1837 / 16000) : ℝ)) ≤ (314532031 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1837 / 16000)) (314532031 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((140682665491 / 1000000) : ℝ) ≤ Real.exp (3 * (3951421 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3951421 / 1000000)) (140682665491 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((367 / 3200) : ℝ) (1837 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3951421 / 1000000) (494067 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (367 / 3200) (1837 / 16000) (125781363 / 100000000) (314532031 / 250000000) (3951421 / 1000000) (494067 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (367 / 3200) (1837 / 16000) (3951421 / 1000000) (494067 / 125000) (38739 / 1000) (19391 / 500)
    (42083 / 500) (42433 / 500) (-143859 / 250) (225627 / 1000000) (3905021 / 1000) (1819699 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3951421 / 1000000) (140682665491 / 1000000) (1819699 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3951421 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3951421 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell128 :
    ∀ t ∈ Set.Icc ((1837 / 16000) : ℝ) (1839 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1258128123 / 1000000000) : ℝ) ≤ Real.exp (2 * (1837 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1837 / 16000)) (1258128123 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1839 / 16000) : ℝ)) ≤ (251688539 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1839 / 16000)) (251688539 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((28220053357 / 200000) : ℝ) ≤ Real.exp (3 * (3952409 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3952409 / 1000000)) (28220053357 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1837 / 16000) : ℝ) (1839 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3952409 / 1000000) (988381 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1837 / 16000) (1839 / 16000) (1258128123 / 1000000000) (251688539 / 200000000) (3952409 / 1000000) (988381 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1837 / 16000) (1839 / 16000) (3952409 / 1000000) (988381 / 250000) (7753 / 200) (38807 / 1000)
    (84317 / 1000) (85017 / 1000) (-575463 / 1000) (28141 / 125000) (3908927 / 1000) (1814313 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3952409 / 1000000) (28220053357 / 200000) (1814313 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3952409 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3952409 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell129 :
    ∀ t ∈ Set.Icc ((1839 / 16000) : ℝ) (1841 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((629221347 / 500000000) : ℝ) ≤ Real.exp (2 * (1839 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1839 / 16000)) (629221347 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1841 / 16000) : ℝ)) ≤ (251751469 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1841 / 16000)) (251751469 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((884494423 / 6250) : ℝ) ≤ Real.exp (3 * (3953397 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3953397 / 1000000)) (884494423 / 6250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1839 / 16000) : ℝ) (1841 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3953397 / 1000000) (3954513 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1839 / 16000) (1841 / 16000) (629221347 / 500000000) (251751469 / 200000000) (3953397 / 1000000) (3954513 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1839 / 16000) (1841 / 16000) (3953397 / 1000000) (3954513 / 1000000) (3879 / 100) (38833 / 1000)
    (84467 / 1000) (85169 / 1000) (-143871 / 250) (224631 / 1000000) (97821 / 25) (113059 / 62500000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3953397 / 1000000) (884494423 / 6250) (113059 / 62500000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3953397 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3953397 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell130 :
    ∀ t ∈ Set.Icc ((1841 / 16000) : ℝ) (1843 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((39336167 / 31250000) : ℝ) ≤ Real.exp (2 * (1841 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1841 / 16000)) (39336167 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1843 / 16000) : ℝ)) ≤ (629536037 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1843 / 16000)) (629536037 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((70969808837 / 500000) : ℝ) ≤ Real.exp (3 * (1977193 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1977193 / 500000)) (70969808837 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1841 / 16000) : ℝ) (1843 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1977193 / 500000) (3955501 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1841 / 16000) (1843 / 16000) (39336167 / 31250000) (629536037 / 500000000) (1977193 / 500000) (3955501 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1841 / 16000) (1843 / 16000) (1977193 / 500000) (3955501 / 1000000) (7763 / 200) (19429 / 500)
    (84619 / 1000) (2133 / 25) (-115103 / 200) (224133 / 1000000) (489594 / 125) (28181 / 15625000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1977193 / 500000) (70969808837 / 500000) (28181 / 15625000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1977193 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1977193 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell131 :
    ∀ t ∈ Set.Icc ((1843 / 16000) : ℝ) (369 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1259072073 / 1000000000) : ℝ) ≤ Real.exp (2 * (1843 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1843 / 16000)) (1259072073 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((369 / 3200) : ℝ)) ≤ (1259386881 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (369 / 3200)) (1259386881 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((35590237521 / 250000) : ℝ) ≤ Real.exp (3 * (1977687 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1977687 / 500000)) (35590237521 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1843 / 16000) : ℝ) (369 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1977687 / 500000) (395649 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1843 / 16000) (369 / 3200) (1259072073 / 1000000000) (1259386881 / 1000000000) (1977687 / 500000) (395649 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1843 / 16000) (369 / 3200) (1977687 / 500000) (395649 / 100000) (971 / 25) (9721 / 250)
    (8477 / 100) (10684 / 125) (-287767 / 500) (223637 / 1000000) (392067 / 100) (899123 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1977687 / 500000) (35590237521 / 250000) (899123 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1977687 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1977687 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell132 :
    ∀ t ∈ Set.Icc ((369 / 3200) : ℝ) (1847 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((491948 / 390625) : ℝ) ≤ Real.exp (2 * (369 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (369 / 3200)) (491948 / 390625) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1847 / 16000) : ℝ)) ≤ (1259701767 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1847 / 16000)) (1259701767 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((71391980761 / 500000) : ℝ) ≤ Real.exp (3 * (3956363 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3956363 / 1000000)) (71391980761 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((369 / 3200) : ℝ) (1847 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3956363 / 1000000) (98937 / 25000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (369 / 3200) (1847 / 16000) (491948 / 390625) (1259701767 / 1000000000) (3956363 / 1000000) (98937 / 25000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (369 / 3200) (1847 / 16000) (3956363 / 1000000) (98937 / 25000) (19433 / 500) (38909 / 1000)
    (84921 / 1000) (10703 / 125) (-575553 / 1000) (111571 / 500000) (981149 / 250) (1792919 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3956363 / 1000000) (71391980761 / 500000) (1792919 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3956363 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3956363 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell133 :
    ∀ t ∈ Set.Icc ((1847 / 16000) : ℝ) (1849 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((629850883 / 500000000) : ℝ) ≤ Real.exp (2 * (1847 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1847 / 16000)) (629850883 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1849 / 16000) : ℝ)) ≤ (315004183 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1849 / 16000)) (315004183 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((35802164879 / 250000) : ℝ) ≤ Real.exp (3 * (3957353 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3957353 / 1000000)) (35802164879 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1847 / 16000) : ℝ) (1849 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3957353 / 1000000) (3958469 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1847 / 16000) (1849 / 16000) (629850883 / 500000000) (315004183 / 250000000) (3957353 / 1000000) (3958469 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1847 / 16000) (1849 / 16000) (3957353 / 1000000) (3958469 / 1000000) (38891 / 1000) (19467 / 500)
    (85073 / 1000) (3431 / 40) (-287791 / 500) (222647 / 1000000) (3928521 / 1000) (893801 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3957353 / 1000000) (35802164879 / 250000) (893801 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3957353 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3957353 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell134 :
    ∀ t ∈ Set.Icc ((1849 / 16000) : ℝ) (1851 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1260016731 / 1000000000) : ℝ) ≤ Real.exp (2 * (1849 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1849 / 16000)) (1260016731 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1851 / 16000) : ℝ)) ≤ (4923171 / 3906250) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1851 / 16000)) (4923171 / 3906250) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((143634189831 / 1000000) : ℝ) ≤ Real.exp (3 * (1979171 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1979171 / 500000)) (143634189831 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1849 / 16000) : ℝ) (1851 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1979171 / 500000) (3959459 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1849 / 16000) (1851 / 16000) (1260016731 / 1000000000) (4923171 / 3906250) (1979171 / 500000) (3959459 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1849 / 16000) (1851 / 16000) (1979171 / 500000) (3959459 / 1000000) (38917 / 1000) (974 / 25)
    (3409 / 40) (10741 / 125) (-2878 / 5) (111077 / 500000) (983113 / 250) (891153 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1979171 / 500000) (143634189831 / 1000000) (891153 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1979171 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1979171 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell135 :
    ∀ t ∈ Set.Icc ((1851 / 16000) : ℝ) (1853 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((50413271 / 40000000) : ℝ) ≤ Real.exp (2 * (1851 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1851 / 16000)) (50413271 / 40000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1853 / 16000) : ℝ)) ≤ (630323449 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1853 / 16000)) (630323449 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((72030708373 / 500000) : ℝ) ≤ Real.exp (3 * (989833 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (989833 / 250000)) (72030708373 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1851 / 16000) : ℝ) (1853 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (989833 / 250000) (3960449 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1851 / 16000) (1853 / 16000) (50413271 / 40000000) (630323449 / 500000000) (989833 / 250000) (3960449 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1851 / 16000) (1853 / 16000) (989833 / 250000) (3960449 / 1000000) (19471 / 500) (7797 / 200)
    (85377 / 1000) (2152 / 25) (-287811 / 500) (110831 / 500000) (3936387 / 1000) (88851 / 50000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (989833 / 250000) (72030708373 / 500000) (88851 / 50000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (989833 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (989833 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell136 :
    ∀ t ∈ Set.Icc ((1853 / 16000) : ℝ) (371 / 3200), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1260646897 / 1000000000) : ℝ) ≤ Real.exp (2 * (1853 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1853 / 16000)) (1260646897 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((371 / 3200) : ℝ)) ≤ (1260962099 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (371 / 3200)) (1260962099 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((72244957203 / 500000) : ℝ) ≤ Real.exp (3 * (1980161 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1980161 / 500000)) (72244957203 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1853 / 16000) : ℝ) (371 / 3200),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1980161 / 500000) (3961439 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1853 / 16000) (371 / 3200) (1260646897 / 1000000000) (1260962099 / 1000000000) (1980161 / 500000) (3961439 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1853 / 16000) (371 / 3200) (1980161 / 500000) (3961439 / 1000000) (38967 / 1000) (39011 / 1000)
    (85529 / 1000) (10779 / 125) (-575643 / 1000) (22117 / 100000) (985081 / 250) (7087 / 4000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1980161 / 500000) (72244957203 / 500000) (7087 / 4000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1980161 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1980161 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell137 :
    ∀ t ∈ Set.Icc ((371 / 3200) : ℝ) (1857 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((630481049 / 500000000) : ℝ) ≤ Real.exp (2 * (371 / 3200)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (371 / 3200)) (630481049 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1857 / 16000) : ℝ)) ≤ (1261277379 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1857 / 16000)) (1261277379 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((144919686589 / 1000000) : ℝ) ≤ Real.exp (3 * (123791 / 31250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (123791 / 31250)) (144919686589 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((371 / 3200) : ℝ) (1857 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (123791 / 31250) (396243 / 100000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (371 / 3200) (1857 / 16000) (630481049 / 500000000) (1261277379 / 1000000000) (123791 / 31250) (396243 / 100000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (371 / 3200) (1857 / 16000) (123791 / 31250) (396243 / 100000) (38993 / 1000) (9759 / 250)
    (85681 / 1000) (17277 / 200) (-575659 / 1000) (5517 / 25000) (986067 / 250) (55203 / 31250000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (123791 / 31250) (144919686589 / 1000000) (55203 / 31250000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (123791 / 31250)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (123791 / 31250)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell138 :
    ∀ t ∈ Set.Icc ((1857 / 16000) : ℝ) (1859 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((630638689 / 500000000) : ℝ) ≤ Real.exp (2 * (1857 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1857 / 16000)) (630638689 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1859 / 16000) : ℝ)) ≤ (630796369 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1859 / 16000)) (630796369 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((145350737087 / 1000000) : ℝ) ≤ Real.exp (3 * (1981151 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1981151 / 500000)) (145350737087 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1857 / 16000) : ℝ) (1859 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1981151 / 500000) (198171 / 50000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1857 / 16000) (1859 / 16000) (630638689 / 500000000) (630796369 / 500000000) (1981151 / 500000) (198171 / 50000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1857 / 16000) (1859 / 16000) (1981151 / 500000) (198171 / 50000) (19509 / 500) (39061 / 1000)
    (85833 / 1000) (43269 / 500) (-575679 / 1000) (22019 / 100000) (987053 / 250) (1761257 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1981151 / 500000) (145350737087 / 1000000) (1761257 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1981151 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1981151 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityExpCompact_cell139 :
    ∀ t ∈ Set.Icc ((1859 / 16000) : ℝ) (1861 / 16000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1261592737 / 1000000000) : ℝ) ≤ Real.exp (2 * (1859 / 16000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1859 / 16000)) (1261592737 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1861 / 16000) : ℝ)) ≤ (78869261 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1861 / 16000)) (78869261 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((145783507051 / 1000000) : ℝ) ≤ Real.exp (3 * (3963293 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3963293 / 1000000)) (145783507051 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1859 / 16000) : ℝ) (1861 / 16000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3963293 / 1000000) (3964411 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1859 / 16000) (1861 / 16000) (1261592737 / 1000000000) (78869261 / 62500000) (3963293 / 1000000) (3964411 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1859 / 16000) (1861 / 16000) (3963293 / 1000000) (3964411 / 1000000) (9761 / 250) (39087 / 1000)
    (42993 / 500) (86691 / 1000) (-575699 / 1000) (219701 / 1000000) (1976081 / 500) (1756029 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3963293 / 1000000) (145783507051 / 1000000) (1756029 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3963293 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3963293 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityExpCompact_cellsBatch006 :
    ∀ t ∈ Set.Icc ((1821 / 16000) : ℝ) (1861 / 16000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell120
      hpThetaDensityExpCompact_cell121)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell122
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell123
      hpThetaDensityExpCompact_cell124)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell125
      hpThetaDensityExpCompact_cell126)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell127
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell128
      hpThetaDensityExpCompact_cell129))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell130
      hpThetaDensityExpCompact_cell131)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell132
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell133
      hpThetaDensityExpCompact_cell134)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell135
      hpThetaDensityExpCompact_cell136)
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell137
      (hpThetaDensityCells_positive_glue hpThetaDensityExpCompact_cell138
      hpThetaDensityExpCompact_cell139)))))

#print axioms hpThetaDensityExpCompact_cellsBatch006
end HodgeProofHP
