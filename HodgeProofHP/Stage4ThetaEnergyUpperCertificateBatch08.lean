import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_160 :
    ∀ u : ℝ, (1 / 5 : ℝ) ≤ u → u ≤ (161 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (62148431 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (1 / 5 : ℝ) (161 / 800 : ℝ) (93239 / 62500 : ℝ) (1495560230761 / 1000000000000 : ℝ)
    (115400753 / 100000000 : ℝ) (10217001 / 1000000000 : ℝ) (62148431 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (1 / 5 : ℝ)) (93239 / 62500 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (161 / 800 : ℝ) (1222931 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (161 / 800 : ℝ))) h 2
    have he :
        (Real.exp (161 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (161 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (93239 / 62500 : ℝ) - (161 / 800 : ℝ) / 2) / 32)
      (115400753 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_161 :
    ∀ u : ℝ, (161 / 800 : ℝ) ≤ u → u ≤ (81 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (123684117 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (161 / 800 : ℝ) (81 / 400 : ℝ) (747779 / 500000 : ℝ) (1499304740521 / 1000000000000 : ℝ)
    (115440789 / 100000000 : ℝ) (101042211 / 10000000000 : ℝ) (123684117 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (161 / 800 : ℝ)) (747779 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (81 / 400 : ℝ) (1224461 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (81 / 400 : ℝ))) h 2
    have he :
        (Real.exp (81 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (81 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (747779 / 500000 : ℝ) - (81 / 400 : ℝ) / 2) / 32)
      (115440789 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_162 :
    ∀ u : ℝ, (81 / 400 : ℝ) ≤ u → u ≤ (163 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (123069453 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (81 / 400 : ℝ) (163 / 800 : ℝ) (749651 / 500000 : ℝ) (23485256001 / 15625000000 : ℝ)
    (14435119 / 12500000 : ℝ) (6245233 / 625000000 : ℝ) (123069453 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (81 / 400 : ℝ)) (749651 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (163 / 800 : ℝ) (153249 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (163 / 800 : ℝ))) h 2
    have he :
        (Real.exp (163 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (163 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (749651 / 500000 : ℝ) - (163 / 800 : ℝ) / 2) / 32)
      (14435119 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_163 :
    ∀ u : ℝ, (163 / 800 : ℝ) ≤ u → u ≤ (41 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (24490903 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (163 / 800 : ℝ) (41 / 200 : ℝ) (300611 / 200000 : ℝ) (376705020169 / 250000000000 : ℝ)
    (115521231 / 100000000 : ℝ) (98814833 / 10000000000 : ℝ) (24490903 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (163 / 800 : ℝ)) (300611 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (41 / 200 : ℝ) (613763 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (41 / 200 : ℝ))) h 2
    have he :
        (Real.exp (41 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (41 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (300611 / 200000 : ℝ) - (41 / 200 : ℝ) / 2) / 32)
      (115521231 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_164 :
    ∀ u : ℝ, (41 / 200 : ℝ) ≤ u → u ≤ (33 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (60919093 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (41 / 200 : ℝ) (33 / 160 : ℝ) (1506817 / 1000000 : ℝ) (1510590941721 / 1000000000000 : ℝ)
    (57780813 / 50000000 : ℝ) (48857743 / 5000000000 : ℝ) (60919093 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (41 / 200 : ℝ)) (1506817 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (33 / 160 : ℝ) (1229061 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (33 / 160 : ℝ))) h 2
    have he :
        (Real.exp (33 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (33 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1506817 / 1000000 : ℝ) - (33 / 160 : ℝ) / 2) / 32)
      (57780813 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_165 :
    ∀ u : ℝ, (33 / 160 : ℝ) ≤ u → u ≤ (83 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (121220691 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (33 / 160 : ℝ) (83 / 400 : ℝ) (1510589 / 1000000 : ℝ) (378592859401 / 250000000000 : ℝ)
    (28900537 / 25000000 : ℝ) (1932507 / 200000000 : ℝ) (121220691 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (33 / 160 : ℝ)) (1510589 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (83 / 400 : ℝ) (615299 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (83 / 400 : ℝ))) h 2
    have he :
        (Real.exp (83 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (83 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1510589 / 1000000 : ℝ) - (83 / 400 : ℝ) / 2) / 32)
      (28900537 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_166 :
    ∀ u : ℝ, (83 / 400 : ℝ) ≤ u → u ≤ (167 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (120602459 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (83 / 400 : ℝ) (167 / 800 : ℝ) (151437 / 100000 : ℝ) (1518161586769 / 1000000000000 : ℝ)
    (115642787 / 100000000 : ℝ) (95544659 / 10000000000 : ℝ) (120602459 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (83 / 400 : ℝ)) (151437 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (167 / 800 : ℝ) (1232137 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (167 / 800 : ℝ))) h 2
    have he :
        (Real.exp (167 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (167 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (151437 / 100000 : ℝ) - (167 / 800 : ℝ) / 2) / 32)
      (115642787 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_167 :
    ∀ u : ℝ, (167 / 800 : ℝ) ≤ u → u ≤ (21 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (59991849 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (167 / 800 : ℝ) (21 / 100 : ℝ) (1518161 / 1000000 : ℝ) (1521963875041 / 1000000000000 : ℝ)
    (57841777 / 50000000 : ℝ) (47236541 / 5000000000 : ℝ) (59991849 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (167 / 800 : ℝ)) (1518161 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (21 / 100 : ℝ) (1233679 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (21 / 100 : ℝ))) h 2
    have he :
        (Real.exp (21 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (21 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1518161 / 1000000 : ℝ) - (21 / 100 : ℝ) / 2) / 32)
      (57841777 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_168 :
    ∀ u : ℝ, (21 / 100 : ℝ) ≤ u → u ≤ (169 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (23872753 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (21 / 100 : ℝ) (169 / 800 : ℝ) (1521961 / 1000000 : ℝ) (381443347321 / 250000000000 : ℝ)
    (115724437 / 100000000 : ℝ) (93410899 / 10000000000 : ℝ) (23872753 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (21 / 100 : ℝ)) (1521961 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (169 / 800 : ℝ) (617611 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (169 / 800 : ℝ))) h 2
    have he :
        (Real.exp (169 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (169 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1521961 / 1000000 : ℝ) - (169 / 800 : ℝ) / 2) / 32)
      (115724437 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_169 :
    ∀ u : ℝ, (169 / 800 : ℝ) ≤ u → u ≤ (17 / 80 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (118742811 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (169 / 800 : ℝ) (17 / 80 : ℝ) (1525771 / 1000000 : ℝ) (1529592612289 / 1000000000000 : ℝ)
    (115765449 / 100000000 : ℝ) (92357733 / 10000000000 : ℝ) (118742811 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (169 / 800 : ℝ)) (1525771 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (17 / 80 : ℝ) (1236767 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (17 / 80 : ℝ))) h 2
    have he :
        (Real.exp (17 / 80 : ℝ)) ^ 2 =
          Real.exp (2 * (17 / 80 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1525771 / 1000000 : ℝ) - (17 / 80 : ℝ) / 2) / 32)
      (115765449 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_170 :
    ∀ u : ℝ, (17 / 80 : ℝ) ≤ u → u ≤ (171 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (118121353 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (17 / 80 : ℝ) (171 / 800 : ℝ) (152959 / 100000 : ℝ) (383355390649 / 250000000000 : ℝ)
    (115806577 / 100000000 : ℝ) (91313881 / 10000000000 : ℝ) (118121353 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (17 / 80 : ℝ)) (152959 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (171 / 800 : ℝ) (619157 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (171 / 800 : ℝ))) h 2
    have he :
        (Real.exp (171 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (171 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (152959 / 100000 : ℝ) - (171 / 800 : ℝ) / 2) / 32)
      (115806577 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_171 :
    ∀ u : ℝ, (171 / 800 : ℝ) ≤ u → u ≤ (43 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (58749233 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (171 / 800 : ℝ) (43 / 200 : ℝ) (1533419 / 1000000 : ℝ) (384314444761 / 250000000000 : ℝ)
    (115847833 / 100000000 : ℝ) (90279 / 10000000 : ℝ) (58749233 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (171 / 800 : ℝ)) (1533419 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (43 / 200 : ℝ) (619931 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (43 / 200 : ℝ))) h 2
    have he :
        (Real.exp (43 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (43 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1533419 / 1000000 : ℝ) - (43 / 200 : ℝ) / 2) / 32)
      (115847833 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_172 :
    ∀ u : ℝ, (43 / 200 : ℝ) ≤ u → u ≤ (173 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (116875659 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (43 / 200 : ℝ) (173 / 800 : ℝ) (1537257 / 1000000 : ℝ) (1541106236569 / 1000000000000 : ℝ)
    (115889207 / 100000000 : ℝ) (89253301 / 10000000000 : ℝ) (116875659 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (43 / 200 : ℝ)) (1537257 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (173 / 800 : ℝ) (1241413 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (173 / 800 : ℝ))) h 2
    have he :
        (Real.exp (173 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (173 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1537257 / 1000000 : ℝ) - (173 / 800 : ℝ) / 2) / 32)
      (115889207 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_173 :
    ∀ u : ℝ, (173 / 800 : ℝ) ≤ u → u ≤ (87 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (58126037 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (173 / 800 : ℝ) (87 / 400 : ℝ) (308221 / 200000 : ℝ) (386241119289 / 250000000000 : ℝ)
    (115930709 / 100000000 : ℝ) (44118249 / 5000000000 : ℝ) (58126037 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (173 / 800 : ℝ)) (308221 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (87 / 400 : ℝ) (621483 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (87 / 400 : ℝ))) h 2
    have he :
        (Real.exp (87 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (87 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (308221 / 200000 : ℝ) - (87 / 400 : ℝ) / 2) / 32)
      (115930709 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_174 :
    ∀ u : ℝ, (87 / 400 : ℝ) ≤ u → u ≤ (7 / 32 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (115627763 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (87 / 400 : ℝ) (7 / 32 : ℝ) (1544963 / 1000000 : ℝ) (1548832519441 / 1000000000000 : ℝ)
    (115972339 / 100000000 : ℝ) (17445711 / 2000000000 : ℝ) (115627763 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (87 / 400 : ℝ)) (1544963 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (7 / 32 : ℝ) (1244521 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (7 / 32 : ℝ))) h 2
    have he :
        (Real.exp (7 / 32 : ℝ)) ^ 2 =
          Real.exp (2 * (7 / 32 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1544963 / 1000000 : ℝ) - (7 / 32 : ℝ) / 2) / 32)
      (115972339 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_175 :
    ∀ u : ℝ, (7 / 32 : ℝ) ≤ u → u ≤ (11 / 50 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (115002599 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (7 / 32 : ℝ) (11 / 50 : ℝ) (154883 / 100000 : ℝ) (1552707889929 / 1000000000000 : ℝ)
    (116014087 / 100000000 : ℝ) (3449187 / 400000000 : ℝ) (115002599 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (7 / 32 : ℝ)) (154883 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (11 / 50 : ℝ) (1246077 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (11 / 50 : ℝ))) h 2
    have he :
        (Real.exp (11 / 50 : ℝ)) ^ 2 =
          Real.exp (2 * (11 / 50 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (154883 / 100000 : ℝ) - (11 / 50 : ℝ) / 2) / 32)
      (116014087 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_176 :
    ∀ u : ℝ, (11 / 50 : ℝ) ≤ u → u ≤ (177 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (114377317 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (11 / 50 : ℝ) (177 / 800 : ℝ) (1552707 / 1000000 : ℝ) (97287224281 / 62500000000 : ℝ)
    (29013991 / 25000000 : ℝ) (17047911 / 2000000000 : ℝ) (114377317 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (11 / 50 : ℝ)) (1552707 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (177 / 800 : ℝ) (311909 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (177 / 800 : ℝ))) h 2
    have he :
        (Real.exp (177 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (177 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1552707 / 1000000 : ℝ) - (177 / 800 : ℝ) / 2) / 32)
      (29013991 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_177 :
    ∀ u : ℝ, (177 / 800 : ℝ) ≤ u → u ≤ (89 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (113751287 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (177 / 800 : ℝ) (89 / 400 : ℝ) (1556593 / 1000000 : ℝ) (97530665401 / 62500000000 : ℝ)
    (116097959 / 100000000 : ℝ) (16851683 / 2000000000 : ℝ) (113751287 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (177 / 800 : ℝ)) (1556593 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (89 / 400 : ℝ) (312299 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (89 / 400 : ℝ))) h 2
    have he :
        (Real.exp (89 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (89 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1556593 / 1000000 : ℝ) - (89 / 400 : ℝ) / 2) / 32)
      (116097959 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_178 :
    ∀ u : ℝ, (89 / 400 : ℝ) ≤ u → u ≤ (179 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (22624971 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (89 / 400 : ℝ) (179 / 800 : ℝ) (156049 / 100000 : ℝ) (1564398076081 / 1000000000000 : ℝ)
    (58070047 / 50000000 : ℝ) (10410713 / 1250000000 : ℝ) (22624971 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (89 / 400 : ℝ)) (156049 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (179 / 800 : ℝ) (1250759 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (179 / 800 : ℝ))) h 2
    have he :
        (Real.exp (179 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (179 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (156049 / 100000 : ℝ) - (179 / 800 : ℝ) / 2) / 32)
      (58070047 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_179 :
    ∀ u : ℝ, (179 / 800 : ℝ) ≤ u → u ≤ (9 / 40 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (14062223 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (179 / 800 : ℝ) (9 / 40 : ℝ) (391099 / 250000 : ℝ) (1568312896329 / 1000000000000 : ℝ)
    (116182347 / 100000000 : ℝ) (82321893 / 10000000000 : ℝ) (14062223 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (179 / 800 : ℝ)) (391099 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (9 / 40 : ℝ) (1252323 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (9 / 40 : ℝ))) h 2
    have he :
        (Real.exp (9 / 40 : ℝ)) ^ 2 =
          Real.exp (2 * (9 / 40 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (391099 / 250000 : ℝ) - (9 / 40 : ℝ) / 2) / 32)
      (116182347 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_160
#print axioms hpThetaEnergyUpper_interval_179

end HodgeProofHP
