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
theorem hpThetaDensityLowerExpCompact_cell800 :
    ∀ t ∈ Set.Icc ((45347 / 512000) : ℝ) (45363 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((149224287 / 125000000) : ℝ) ≤ Real.exp (2 * (45347 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45347 / 512000)) (149224287 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45363 / 512000) : ℝ)) ≤ (1193868911 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45363 / 512000)) (1193868911 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((961875517 / 12500) : ℝ) ≤ Real.exp (3 * (117197 / 31250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (117197 / 31250)) (961875517 / 12500) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45347 / 512000) : ℝ) (45363 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (117197 / 31250) (3750659 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45347 / 512000) (45363 / 512000) (149224287 / 125000000) (1193868911 / 1000000000) (117197 / 31250) (3750659 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45347 / 512000) (45363 / 512000) (117197 / 31250) (3750659 / 1000000) (6751 / 200) (4221 / 125)
    (7026 / 125) (28207 / 500) (-560907 / 1000) (352467 / 1000000) (395786 / 125) (1663417 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (117197 / 31250) (961875517 / 12500) (1663417 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (117197 / 31250)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (117197 / 31250)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell801 :
    ∀ t ∈ Set.Icc ((45363 / 512000) : ℝ) (45379 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((119386891 / 100000000) : ℝ) ≤ Real.exp (2 * (45363 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45363 / 512000)) (119386891 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45379 / 512000) : ℝ)) ≤ (119394353 / 100000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45379 / 512000)) (119394353 / 100000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((38502155117 / 500000) : ℝ) ≤ Real.exp (3 * (3750539 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3750539 / 1000000)) (38502155117 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45363 / 512000) : ℝ) (45379 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3750539 / 1000000) (3750893 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45363 / 512000) (45379 / 512000) (119386891 / 100000000) (119394353 / 100000000) (3750539 / 1000000) (3750893 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45363 / 512000) (45379 / 512000) (3750539 / 1000000) (3750893 / 1000000) (844 / 25) (16887 / 500)
    (56239 / 1000) (14111 / 250) (-560947 / 1000) (88071 / 250000) (1583539 / 500) (332449 / 100000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3750539 / 1000000) (38502155117 / 500000) (332449 / 100000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3750539 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3750539 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell802 :
    ∀ t ∈ Set.Icc ((45379 / 512000) : ℝ) (9079 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1193943529 / 1000000000) : ℝ) ≤ Real.exp (2 * (45379 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45379 / 512000)) (1193943529 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9079 / 102400) : ℝ)) ≤ (597009077 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9079 / 102400)) (597009077 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((15411677241 / 200000) : ℝ) ≤ Real.exp (3 * (3750773 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3750773 / 1000000)) (15411677241 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45379 / 512000) : ℝ) (9079 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3750773 / 1000000) (468891 / 125000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45379 / 512000) (9079 / 102400) (1193943529 / 1000000000) (597009077 / 500000000) (3750773 / 1000000) (468891 / 125000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45379 / 512000) (9079 / 102400) (3750773 / 1000000) (468891 / 125000) (16883 / 500) (1689 / 50)
    (14067 / 250) (28237 / 500) (-560977 / 1000) (352103 / 1000000) (395984 / 125) (3322157 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3750773 / 1000000) (15411677241 / 200000) (3322157 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3750773 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3750773 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell803 :
    ∀ t ∈ Set.Icc ((9079 / 102400) : ℝ) (45411 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1194018153 / 1000000000) : ℝ) ≤ Real.exp (2 * (9079 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9079 / 102400)) (1194018153 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45411 / 512000) : ℝ)) ≤ (597046391 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45411 / 512000)) (597046391 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((2409772859 / 31250) : ℝ) ≤ Real.exp (3 * (117219 / 31250)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (117219 / 31250)) (2409772859 / 31250) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9079 / 102400) : ℝ) (45411 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (117219 / 31250) (1875681 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (9079 / 102400) (45411 / 512000) (1194018153 / 1000000000) (597046391 / 500000000) (117219 / 31250) (1875681 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (9079 / 102400) (45411 / 512000) (117219 / 31250) (1875681 / 500000) (8443 / 250) (6757 / 200)
    (28149 / 500) (7063 / 125) (-70127 / 125) (351921 / 1000000) (1584331 / 500) (663963 / 200000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (117219 / 31250) (2409772859 / 31250) (663963 / 200000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (117219 / 31250)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (117219 / 31250)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell804 :
    ∀ t ∈ Set.Icc ((45411 / 512000) : ℝ) (45427 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1194092781 / 1000000000) : ℝ) ≤ Real.exp (2 * (45411 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45411 / 512000)) (1194092781 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45427 / 512000) : ℝ)) ≤ (149270927 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45427 / 512000)) (149270927 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((38583441799 / 500000) : ℝ) ≤ Real.exp (3 * (1875621 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1875621 / 500000)) (38583441799 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45411 / 512000) : ℝ) (45427 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1875621 / 500000) (3751597 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45411 / 512000) (45427 / 512000) (1194092781 / 1000000000) (149270927 / 125000000) (1875621 / 500000) (3751597 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45411 / 512000) (45427 / 512000) (1875621 / 500000) (3751597 / 1000000) (33777 / 1000) (33791 / 1000)
    (7041 / 125) (28267 / 500) (-280523 / 500) (17587 / 50000) (396182 / 125) (1658743 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1875621 / 500000) (38583441799 / 500000) (1658743 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1875621 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1875621 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell805 :
    ∀ t ∈ Set.Icc ((45427 / 512000) : ℝ) (45443 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((238833483 / 200000000) : ℝ) ≤ Real.exp (2 * (45427 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45427 / 512000)) (238833483 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45443 / 512000) : ℝ)) ≤ (1194242053 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45443 / 512000)) (1194242053 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((15444214747 / 200000) : ℝ) ≤ Real.exp (3 * (937869 / 250000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (937869 / 250000)) (15444214747 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45427 / 512000) : ℝ) (45443 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (937869 / 250000) (3751831 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45427 / 512000) (45443 / 512000) (238833483 / 200000000) (1194242053 / 1000000000) (937869 / 250000) (3751831 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45427 / 512000) (45443 / 512000) (937869 / 250000) (3751831 / 1000000) (33783 / 1000) (33797 / 1000)
    (28179 / 500) (14141 / 250) (-561081 / 1000) (351559 / 1000000) (3170247 / 1000) (1657579 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (937869 / 250000) (15444214747 / 200000) (1657579 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (937869 / 250000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (937869 / 250000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell806 :
    ∀ t ∈ Set.Icc ((45443 / 512000) : ℝ) (45459 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((298560513 / 250000000) : ℝ) ≤ Real.exp (2 * (45443 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45443 / 512000)) (298560513 / 250000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45459 / 512000) : ℝ)) ≤ (149289587 / 125000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45459 / 512000)) (149289587 / 125000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((38637766877 / 500000) : ℝ) ≤ Real.exp (3 * (3751711 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3751711 / 1000000)) (38637766877 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45443 / 512000) : ℝ) (45459 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3751711 / 1000000) (1876033 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45443 / 512000) (45459 / 512000) (298560513 / 250000000) (149289587 / 125000000) (3751711 / 1000000) (1876033 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45443 / 512000) (45459 / 512000) (3751711 / 1000000) (1876033 / 500000) (8447 / 250) (16901 / 500)
    (14097 / 250) (28297 / 500) (-140279 / 250) (351377 / 1000000) (1585521 / 500) (3312821 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3751711 / 1000000) (38637766877 / 500000) (3312821 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3751711 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3751711 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell807 :
    ∀ t ∈ Set.Icc ((45459 / 512000) : ℝ) (1819 / 20480), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((238863339 / 200000000) : ℝ) ≤ Real.exp (2 * (45459 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45459 / 512000)) (238863339 / 200000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((1819 / 20480) : ℝ)) ≤ (1194391343 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (1819 / 20480)) (1194391343 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((7732980019 / 100000) : ℝ) ≤ Real.exp (3 * (750389 / 200000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (750389 / 200000)) (7732980019 / 100000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45459 / 512000) : ℝ) (1819 / 20480),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (750389 / 200000) (37523 / 10000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45459 / 512000) (1819 / 20480) (238863339 / 200000000) (1194391343 / 1000000000) (750389 / 200000) (37523 / 10000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45459 / 512000) (1819 / 20480) (750389 / 200000) (37523 / 10000) (16897 / 500) (4226 / 125)
    (28209 / 500) (7078 / 125) (-561151 / 1000) (351197 / 1000000) (3171833 / 1000) (3310497 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (750389 / 200000) (7732980019 / 100000) (3310497 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (750389 / 200000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (750389 / 200000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell808 :
    ∀ t ∈ Set.Icc ((1819 / 20480) : ℝ) (45491 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((597195671 / 500000000) : ℝ) ≤ Real.exp (2 * (1819 / 20480)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (1819 / 20480)) (597195671 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45491 / 512000) : ℝ)) ≤ (238893199 / 200000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45491 / 512000)) (238893199 / 200000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((9673042111 / 125000) : ℝ) ≤ Real.exp (3 * (187609 / 50000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (187609 / 50000)) (9673042111 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((1819 / 20480) : ℝ) (45491 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (187609 / 50000) (750507 / 200000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (1819 / 20480) (45491 / 512000) (597195671 / 500000000) (238893199 / 200000000) (187609 / 50000) (750507 / 200000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (1819 / 20480) (45491 / 512000) (187609 / 50000) (750507 / 200000) (169 / 5) (33813 / 1000)
    (7056 / 125) (28327 / 500) (-112237 / 200) (70203 / 200000) (3172627 / 1000) (3308163 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (187609 / 50000) (9673042111 / 125000) (3308163 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (187609 / 50000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (187609 / 50000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell809 :
    ∀ t ∈ Set.Icc ((45491 / 512000) : ℝ) (45507 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((597232997 / 500000000) : ℝ) ≤ Real.exp (2 * (45491 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45491 / 512000)) (597232997 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45507 / 512000) : ℝ)) ≤ (1194540651 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45507 / 512000)) (1194540651 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((77438679731 / 1000000) : ℝ) ≤ Real.exp (3 * (1876207 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1876207 / 500000)) (77438679731 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45491 / 512000) : ℝ) (45507 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1876207 / 500000) (3752769 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45491 / 512000) (45507 / 512000) (597232997 / 500000000) (1194540651 / 1000000000) (1876207 / 500000) (3752769 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45491 / 512000) (45507 / 512000) (1876207 / 500000) (3752769 / 1000000) (6761 / 200) (33819 / 1000)
    (28239 / 500) (14171 / 250) (-28061 / 50) (175417 / 500000) (3173419 / 1000) (1652921 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1876207 / 500000) (77438679731 / 1000000) (1652921 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1876207 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1876207 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell810 :
    ∀ t ∈ Set.Icc ((45507 / 512000) : ℝ) (45523 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((23890813 / 20000000) : ℝ) ≤ Real.exp (2 * (45507 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45507 / 512000)) (23890813 / 20000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45523 / 512000) : ℝ)) ≤ (74663457 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45523 / 512000)) (74663457 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((15498658643 / 200000) : ℝ) ≤ Real.exp (3 * (3752649 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3752649 / 1000000)) (15498658643 / 200000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45507 / 512000) : ℝ) (45523 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3752649 / 1000000) (938251 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45507 / 512000) (45523 / 512000) (23890813 / 20000000) (74663457 / 62500000) (3752649 / 1000000) (938251 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45507 / 512000) (45523 / 512000) (3752649 / 1000000) (938251 / 250000) (33811 / 1000) (1353 / 40)
    (14127 / 250) (28357 / 500) (-112251 / 200) (350653 / 1000000) (1587107 / 500) (412939 / 125000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3752649 / 1000000) (15498658643 / 200000) (412939 / 125000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3752649 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3752649 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell811 :
    ∀ t ∈ Set.Icc ((45523 / 512000) : ℝ) (45539 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1194615311 / 1000000000) : ℝ) ≤ Real.exp (2 * (45523 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45523 / 512000)) (1194615311 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45539 / 512000) : ℝ)) ≤ (597344989 / 500000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45539 / 512000)) (597344989 / 500000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((19386928143 / 250000) : ℝ) ≤ Real.exp (3 * (3752883 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3752883 / 1000000)) (19386928143 / 250000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45523 / 512000) : ℝ) (45539 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3752883 / 1000000) (3753239 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45523 / 512000) (45539 / 512000) (1194615311 / 1000000000) (597344989 / 500000000) (3752883 / 1000000) (3753239 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45523 / 512000) (45539 / 512000) (3752883 / 1000000) (3753239 / 1000000) (33817 / 1000) (3383 / 100)
    (56537 / 1000) (7093 / 125) (-140321 / 250) (350473 / 1000000) (3175009 / 1000) (1650597 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3752883 / 1000000) (19386928143 / 250000) (1650597 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3752883 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3752883 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell812 :
    ∀ t ∈ Set.Icc ((45539 / 512000) : ℝ) (9111 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1194689977 / 1000000000) : ℝ) ≤ Real.exp (2 * (45539 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45539 / 512000)) (1194689977 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9111 / 102400) : ℝ)) ≤ (1194764649 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9111 / 102400)) (1194764649 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((9700300369 / 125000) : ℝ) ≤ Real.exp (3 * (1876559 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1876559 / 500000)) (9700300369 / 125000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45539 / 512000) : ℝ) (9111 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1876559 / 500000) (3753473 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45539 / 512000) (9111 / 102400) (1194689977 / 1000000000) (1194764649 / 1000000000) (1876559 / 500000) (3753473 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45539 / 512000) (9111 / 102400) (1876559 / 500000) (3753473 / 1000000) (16911 / 500) (8459 / 250)
    (7071 / 125) (28387 / 500) (-140331 / 250) (350291 / 1000000) (3175801 / 1000) (3298867 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1876559 / 500000) (9700300369 / 125000) (3298867 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1876559 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1876559 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell813 :
    ∀ t ∈ Set.Icc ((9111 / 102400) : ℝ) (45571 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((149345581 / 125000000) : ℝ) ≤ Real.exp (2 * (9111 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9111 / 102400)) (149345581 / 125000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45571 / 512000) : ℝ)) ≤ (298709831 / 250000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45571 / 512000)) (298709831 / 250000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((38828565951 / 500000) : ℝ) ≤ Real.exp (3 * (3753353 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3753353 / 1000000)) (38828565951 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9111 / 102400) : ℝ) (45571 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3753353 / 1000000) (938427 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (9111 / 102400) (45571 / 512000) (149345581 / 125000000) (298709831 / 250000000) (3753353 / 1000000) (938427 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (9111 / 102400) (45571 / 512000) (3753353 / 1000000) (938427 / 250000) (8457 / 250) (16921 / 500)
    (28299 / 500) (14201 / 250) (-280679 / 500) (35011 / 100000) (794149 / 250) (3296543 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3753353 / 1000000) (38828565951 / 500000) (3296543 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3753353 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3753353 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell814 :
    ∀ t ∈ Set.Icc ((45571 / 512000) : ℝ) (45587 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1194839323 / 1000000000) : ℝ) ≤ Real.exp (2 * (45571 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45571 / 512000)) (1194839323 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45587 / 512000) : ℝ)) ≤ (1194914003 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45587 / 512000)) (1194914003 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((38855833157 / 500000) : ℝ) ≤ Real.exp (3 * (3753587 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3753587 / 1000000)) (38855833157 / 500000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45571 / 512000) : ℝ) (45587 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3753587 / 1000000) (1876971 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45571 / 512000) (45587 / 512000) (1194839323 / 1000000000) (1194914003 / 1000000000) (3753587 / 1000000) (1876971 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45571 / 512000) (45587 / 512000) (3753587 / 1000000) (1876971 / 500000) (16917 / 500) (33847 / 1000)
    (14157 / 250) (28417 / 500) (-561393 / 1000) (34993 / 100000) (794347 / 250) (3294229 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3753587 / 1000000) (38855833157 / 500000) (3294229 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3753587 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3753587 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell815 :
    ∀ t ∈ Set.Icc ((45587 / 512000) : ℝ) (45603 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((597457001 / 500000000) : ℝ) ≤ Real.exp (2 * (45587 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45587 / 512000)) (597457001 / 500000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45603 / 512000) : ℝ)) ≤ (74686793 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45603 / 512000)) (74686793 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((77766472321 / 1000000) : ℝ) ≤ Real.exp (3 * (1876911 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1876911 / 500000)) (77766472321 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45587 / 512000) : ℝ) (45603 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1876911 / 500000) (3754177 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45587 / 512000) (45603 / 512000) (597457001 / 500000000) (74686793 / 62500000) (1876911 / 500000) (3754177 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45587 / 512000) (45603 / 512000) (1876911 / 500000) (3754177 / 1000000) (33839 / 1000) (33853 / 1000)
    (28329 / 500) (7108 / 125) (-561427 / 1000) (349749 / 1000000) (397273 / 125) (822977 / 250000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1876911 / 500000) (77766472321 / 1000000) (822977 / 250000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1876911 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1876911 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell816 :
    ∀ t ∈ Set.Icc ((45603 / 512000) : ℝ) (45619 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((1194988687 / 1000000000) : ℝ) ≤ Real.exp (2 * (45603 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45603 / 512000)) (1194988687 / 1000000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45619 / 512000) : ℝ)) ≤ (1195063377 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45619 / 512000)) (1195063377 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((77821083517 / 1000000) : ℝ) ≤ Real.exp (3 * (469257 / 125000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (469257 / 125000)) (77821083517 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45603 / 512000) : ℝ) (45619 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (469257 / 125000) (938603 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45603 / 512000) (45619 / 512000) (1194988687 / 1000000000) (1195063377 / 1000000000) (469257 / 125000) (938603 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45603 / 512000) (45619 / 512000) (469257 / 125000) (938603 / 250000) (6769 / 200) (33859 / 1000)
    (56687 / 1000) (28447 / 500) (-561457 / 1000) (349569 / 1000000) (158949 / 50) (3289597 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (469257 / 125000) (77821083517 / 1000000) (3289597 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (469257 / 125000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (469257 / 125000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell817 :
    ∀ t ∈ Set.Icc ((45619 / 512000) : ℝ) (9127 / 102400), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((74691461 / 62500000) : ℝ) ≤ Real.exp (2 * (45619 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45619 / 512000)) (74691461 / 62500000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((9127 / 102400) : ℝ)) ≤ (1195138071 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (9127 / 102400)) (1195138071 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((77875966691 / 1000000) : ℝ) ≤ Real.exp (3 * (3754291 / 1000000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (3754291 / 1000000)) (77875966691 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45619 / 512000) : ℝ) (9127 / 102400),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (3754291 / 1000000) (1877323 / 500000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45619 / 512000) (9127 / 102400) (74691461 / 62500000) (1195138071 / 1000000000) (3754291 / 1000000) (1877323 / 500000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45619 / 512000) (9127 / 102400) (3754291 / 1000000) (1877323 / 500000) (677 / 20) (4233 / 125)
    (28359 / 500) (14231 / 250) (-70187 / 125) (87347 / 250000) (794943 / 250) (3287279 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (3754291 / 1000000) (77875966691 / 1000000) (3287279 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3754291 / 1000000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3754291 / 1000000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell818 :
    ∀ t ∈ Set.Icc ((9127 / 102400) : ℝ) (45651 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((119513807 / 100000000) : ℝ) ≤ Real.exp (2 * (9127 / 102400)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (9127 / 102400)) (119513807 / 100000000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45651 / 512000) : ℝ)) ≤ (1195212769 / 1000000000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45651 / 512000)) (1195212769 / 1000000000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((77930888571 / 1000000) : ℝ) ≤ Real.exp (3 * (1877263 / 500000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (1877263 / 500000)) (77930888571 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((9127 / 102400) : ℝ) (45651 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (1877263 / 500000) (3754881 / 1000000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (9127 / 102400) (45651 / 512000) (119513807 / 100000000) (1195212769 / 1000000000) (1877263 / 500000) (3754881 / 1000000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (9127 / 102400) (45651 / 512000) (1877263 / 500000) (3754881 / 1000000) (4232 / 125) (3387 / 100)
    (14187 / 250) (28477 / 500) (-561531 / 1000) (349207 / 1000000) (3180569 / 1000) (1642481 / 500000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (1877263 / 500000) (77930888571 / 1000000) (1642481 / 500000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1877263 / 500000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1877263 / 500000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

set_option maxHeartbeats 2000000 in
-- Rational Taylor certificates and signed polynomial interval arithmetic.
theorem hpThetaDensityLowerExpCompact_cell819 :
    ∀ t ∈ Set.Icc ((45651 / 512000) : ℝ) (45667 / 512000), 0 < hpThetaPhiDensityCurvature t := by
  have heL : ((37350399 / 31250000) : ℝ) ≤ Real.exp (2 * (45651 / 512000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (2 * (45651 / 512000)) (37350399 / 31250000) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have heU : Real.exp (2 * ((45667 / 512000) : ℝ)) ≤ (74705467 / 62500000) := by
    exact hpThetaTrace_exp_upper_of_taylor (2 * (45667 / 512000)) (74705467 / 62500000) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
        Finset.sum_range_succ, Nat.factorial])
  have hv : ((77985615227 / 1000000) : ℝ) ≤ Real.exp (3 * (93869 / 25000)) := by
    exact hpThetaTrace_exp_lower_of_taylor (3 * (93869 / 25000)) (77985615227 / 1000000) 32
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have hb : ∀ t ∈ Set.Icc ((45651 / 512000) : ℝ) (45667 / 512000),
      Real.pi * Real.exp (2 * t) ∈ Set.Icc (93869 / 25000) (938779 / 250000) := by
    intro t ht
    exact hpThetaDensityCells_parameter_bounds
      (45651 / 512000) (45667 / 512000) (37350399 / 31250000) (74705467 / 62500000) (93869 / 25000) (938779 / 250000) t
      ht (by norm_num) heL heU (by norm_num) (by norm_num)
  apply hpThetaDensityExpCells_interval_certificate
    (45651 / 512000) (45667 / 512000) (93869 / 25000) (938779 / 250000) (16931 / 500) (8469 / 250)
    (28389 / 500) (11397 / 200) (-14039 / 25) (87257 / 250000) (636273 / 200) (3282657 / 1000000000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hb
  · intro t ht
    exact hpThetaDensityCells_ratio_bound (93869 / 25000) (77985615227 / 1000000) (3282657 / 1000000000)
      (Real.pi * Real.exp (2 * t)) (hb t ht).1
      (by norm_num) (by norm_num) hv (by norm_num)
  · intro b hb'
    have hb0 : 0 ≤ b := by linarith [hb'.1]
    have h2L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (93869 / 25000)) hb'.1 2
    have h3L := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (93869 / 25000)) hb'.1 3
    have h2U := pow_le_pow_left₀ hb0 hb'.2 2
    have h3U := pow_le_pow_left₀ hb0 hb'.2 3
    have h4U := pow_le_pow_left₀ hb0 hb'.2 4
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hb'.1, hb'.2, h2L, h3L, h2U, h3U, h4U]
  · norm_num [hpThetaDensityCurvatureBoxMargin]

theorem hpThetaDensityLowerExpCompact_cellsBatch040 :
    ∀ t ∈ Set.Icc ((45347 / 512000) : ℝ) (45667 / 512000),
      0 < hpThetaPhiDensityCurvature t := by
  exact (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell800
      hpThetaDensityLowerExpCompact_cell801)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell802
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell803
      hpThetaDensityLowerExpCompact_cell804)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell805
      hpThetaDensityLowerExpCompact_cell806)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell807
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell808
      hpThetaDensityLowerExpCompact_cell809))))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell810
      hpThetaDensityLowerExpCompact_cell811)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell812
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell813
      hpThetaDensityLowerExpCompact_cell814)))
      (hpThetaDensityCells_positive_glue (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell815
      hpThetaDensityLowerExpCompact_cell816)
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell817
      (hpThetaDensityCells_positive_glue hpThetaDensityLowerExpCompact_cell818
      hpThetaDensityLowerExpCompact_cell819)))))

#print axioms hpThetaDensityLowerExpCompact_cellsBatch040
end HodgeProofHP
