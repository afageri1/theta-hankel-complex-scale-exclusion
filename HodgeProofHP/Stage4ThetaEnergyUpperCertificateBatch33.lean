import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_660 :
    ∀ u : ℝ, (33 / 40 : ℝ) ≤ u → u ≤ (661 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (5911 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (33 / 40 : ℝ) (661 / 800 : ℝ) (2603489 / 500000 : ℝ) (208800560809 / 40000000000 : ℝ)
    (164546753 / 100000000 : ℝ) (1199 / 10000000000 : ℝ) (5911 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (33 / 40 : ℝ)) (2603489 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (661 / 800 : ℝ) (456947 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (661 / 800 : ℝ))) h 2
    have he :
        (Real.exp (661 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (661 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2603489 / 500000 : ℝ) - (661 / 800 : ℝ) / 2) / 32)
      (164546753 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_661 :
    ∀ u : ℝ, (661 / 800 : ℝ) ≤ u → u ≤ (331 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (22837 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (661 / 800 : ℝ) (331 / 400 : ℝ) (1305003 / 250000 : ℝ) (5233081733649 / 1000000000000 : ℝ)
    (164754119 / 100000000 : ℝ) (9 / 78125000 : ℝ) (22837 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (661 / 800 : ℝ)) (1305003 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (331 / 400 : ℝ) (2287593 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (331 / 400 : ℝ))) h 2
    have he :
        (Real.exp (331 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (331 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1305003 / 250000 : ℝ) - (331 / 400 : ℝ) / 2) / 32)
      (164754119 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_662 :
    ∀ u : ℝ, (331 / 400 : ℝ) ≤ u → u ≤ (663 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (22041 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (331 / 400 : ℝ) (663 / 800 : ℝ) (2616539 / 500000 : ℝ) (1311544881529 / 250000000000 : ℝ)
    (20620283 / 12500000 : ℝ) (553 / 5000000000 : ℝ) (22041 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (331 / 400 : ℝ)) (2616539 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (663 / 800 : ℝ) (1145227 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (663 / 800 : ℝ))) h 2
    have he :
        (Real.exp (663 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (663 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2616539 / 500000 : ℝ) - (663 / 800 : ℝ) / 2) / 32)
      (20620283 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_663 :
    ∀ u : ℝ, (663 / 800 : ℝ) ≤ u → u ≤ (83 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (851 / 4000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (663 / 800 : ℝ) (83 / 100 : ℝ) (5246177 / 1000000 : ℝ) (5259312035761 / 1000000000000 : ℝ)
    (82585603 / 50000000 : ℝ) (531 / 5000000000 : ℝ) (851 / 4000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (663 / 800 : ℝ)) (5246177 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (83 / 100 : ℝ) (2293319 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (83 / 100 : ℝ))) h 2
    have he :
        (Real.exp (83 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (83 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (5246177 / 1000000 : ℝ) - (83 / 100 : ℝ) / 2) / 32)
      (82585603 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_664 :
    ∀ u : ℝ, (83 / 100 : ℝ) ≤ u → u ≤ (133 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (20541 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (83 / 100 : ℝ) (133 / 160 : ℝ) (5259309 / 1000000 : ℝ) (329529958209 / 62500000000 : ℝ)
    (165380949 / 100000000 : ℝ) (51 / 500000000 : ℝ) (20541 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (83 / 100 : ℝ)) (5259309 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (133 / 160 : ℝ) (574047 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (133 / 160 : ℝ))) h 2
    have he :
        (Real.exp (133 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (133 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (5259309 / 1000000 : ℝ) - (133 / 160 : ℝ) / 2) / 32)
      (165380949 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_665 :
    ∀ u : ℝ, (133 / 160 : ℝ) ≤ u → u ≤ (333 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (31 / 156250 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (133 / 160 : ℝ) (333 / 400 : ℝ) (2636237 / 500000 : ℝ) (13214192209 / 2500000000 : ℝ)
    (33118299 / 20000000 : ℝ) (49 / 500000000 : ℝ) (31 / 156250 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (133 / 160 : ℝ)) (2636237 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (333 / 400 : ℝ) (114953 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (333 / 400 : ℝ))) h 2
    have he :
        (Real.exp (333 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (333 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2636237 / 500000 : ℝ) - (333 / 400 : ℝ) / 2) / 32)
      (33118299 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_666 :
    ∀ u : ℝ, (333 / 400 : ℝ) ≤ u → u ≤ (667 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1913 / 10000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (333 / 400 : ℝ) (667 / 800 : ℝ) (660709 / 125000 : ℝ) (211956189769 / 40000000000 : ℝ)
    (33160569 / 20000000 : ℝ) (47 / 500000000 : ℝ) (1913 / 10000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (333 / 400 : ℝ)) (660709 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (667 / 800 : ℝ) (460387 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (667 / 800 : ℝ))) h 2
    have he :
        (Real.exp (667 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (667 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (660709 / 125000 : ℝ) - (667 / 800 : ℝ) / 2) / 32)
      (33160569 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_667 :
    ∀ u : ℝ, (667 / 800 : ℝ) ≤ u → u ≤ (167 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (9237 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (667 / 800 : ℝ) (167 / 200 : ℝ) (2649451 / 500000 : ℝ) (212486887369 / 40000000000 : ℝ)
    (166014987 / 100000000 : ℝ) (903 / 10000000000 : ℝ) (9237 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (667 / 800 : ℝ)) (2649451 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (167 / 200 : ℝ) (460963 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (167 / 200 : ℝ))) h 2
    have he :
        (Real.exp (167 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (167 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2649451 / 500000 : ℝ) - (167 / 200 : ℝ) / 2) / 32)
      (166014987 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_668 :
    ∀ u : ℝ, (167 / 200 : ℝ) ≤ u → u ≤ (669 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1781 / 10000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (167 / 200 : ℝ) (669 / 800 : ℝ) (2656083 / 500000 : ℝ) (5325465443809 / 1000000000000 : ℝ)
    (83113977 / 50000000 : ℝ) (433 / 5000000000 : ℝ) (1781 / 10000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (167 / 200 : ℝ)) (2656083 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (669 / 800 : ℝ) (2307697 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (669 / 800 : ℝ))) h 2
    have he :
        (Real.exp (669 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (669 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2656083 / 500000 : ℝ) - (669 / 800 : ℝ) / 2) / 32)
      (83113977 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_669 :
    ∀ u : ℝ, (669 / 800 : ℝ) ≤ u → u ≤ (67 / 80 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (17201 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (669 / 800 : ℝ) (67 / 80 : ℝ) (5325463 / 1000000 : ℝ) (83418725329 / 15625000000 : ℝ)
    (83220867 / 50000000 : ℝ) (13 / 156250000 : ℝ) (17201 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (669 / 800 : ℝ)) (5325463 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (67 / 80 : ℝ) (288823 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (67 / 80 : ℝ))) h 2
    have he :
        (Real.exp (67 / 80 : ℝ)) ^ 2 =
          Real.exp (2 * (67 / 80 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (5325463 / 1000000 : ℝ) - (67 / 80 : ℝ) / 2) / 32)
      (83220867 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_670 :
    ∀ u : ℝ, (67 / 80 : ℝ) ≤ u → u ≤ (671 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2073 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (67 / 80 : ℝ) (671 / 800 : ℝ) (5338793 / 1000000 : ℝ) (1338040487169 / 250000000000 : ℝ)
    (20832041 / 12500000 : ℝ) (399 / 5000000000 : ℝ) (2073 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (67 / 80 : ℝ)) (5338793 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (671 / 800 : ℝ) (1156737 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (671 / 800 : ℝ))) h 2
    have he :
        (Real.exp (671 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (671 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (5338793 / 1000000 : ℝ) - (671 / 800 : ℝ) / 2) / 32)
      (20832041 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_671 :
    ∀ u : ℝ, (671 / 800 : ℝ) ≤ u → u ≤ (21 / 25 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (16003 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (671 / 800 : ℝ) (21 / 25 : ℝ) (5352157 / 1000000 : ℝ) (5365556078689 / 1000000000000 : ℝ)
    (41717939 / 25000000 : ℝ) (383 / 5000000000 : ℝ) (16003 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (671 / 800 : ℝ)) (5352157 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (21 / 25 : ℝ) (2316367 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (21 / 25 : ℝ))) h 2
    have he :
        (Real.exp (21 / 25 : ℝ)) ^ 2 =
          Real.exp (2 * (21 / 25 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (5352157 / 1000000 : ℝ) - (21 / 25 : ℝ) / 2) / 32)
      (41717939 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_672 :
    ∀ u : ℝ, (21 / 25 : ℝ) ≤ u → u ≤ (673 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (3859 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (21 / 25 : ℝ) (673 / 800 : ℝ) (2682777 / 500000 : ℝ) (215159605609 / 40000000000 : ℝ)
    (167088003 / 100000000 : ℝ) (147 / 2000000000 : ℝ) (3859 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (21 / 25 : ℝ)) (2682777 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (673 / 800 : ℝ) (463853 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (673 / 800 : ℝ))) h 2
    have he :
        (Real.exp (673 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (673 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2682777 / 500000 : ℝ) - (673 / 800 : ℝ) / 2) / 32)
      (167088003 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_673 :
    ∀ u : ℝ, (673 / 800 : ℝ) ≤ u → u ≤ (337 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (3721 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (673 / 800 : ℝ) (337 / 400 : ℝ) (1075797 / 200000 : ℝ) (1348113732889 / 250000000000 : ℝ)
    (167305089 / 100000000 : ℝ) (141 / 2000000000 : ℝ) (3721 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (673 / 800 : ℝ)) (1075797 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (337 / 400 : ℝ) (1161083 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (337 / 400 : ℝ))) h 2
    have he :
        (Real.exp (337 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (337 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1075797 / 200000 : ℝ) - (337 / 400 : ℝ) / 2) / 32)
      (167305089 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_674 :
    ∀ u : ℝ, (337 / 400 : ℝ) ≤ u → u ≤ (27 / 32 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (14347 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (337 / 400 : ℝ) (27 / 32 : ℝ) (5392449 / 1000000 : ℝ) (54059505049 / 10000000000 : ℝ)
    (167522999 / 100000000 : ℝ) (169 / 2500000000 : ℝ) (14347 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (337 / 400 : ℝ)) (5392449 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (27 / 32 : ℝ) (232507 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (27 / 32 : ℝ))) h 2
    have he :
        (Real.exp (27 / 32 : ℝ)) ^ 2 =
          Real.exp (2 * (27 / 32 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (5392449 / 1000000 : ℝ) - (27 / 32 : ℝ) / 2) / 32)
      (167522999 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_675 :
    ∀ u : ℝ, (27 / 32 : ℝ) ≤ u → u ≤ (169 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (553 / 4000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (27 / 32 : ℝ) (169 / 200 : ℝ) (5405947 / 1000000 : ℝ) (1354870392121 / 250000000000 : ℝ)
    (20967719 / 12500000 : ℝ) (81 / 1250000000 : ℝ) (553 / 4000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (27 / 32 : ℝ)) (5405947 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (169 / 200 : ℝ) (1163989 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (169 / 200 : ℝ))) h 2
    have he :
        (Real.exp (169 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (169 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (5405947 / 1000000 : ℝ) - (169 / 200 : ℝ) / 2) / 32)
      (20967719 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_676 :
    ∀ u : ℝ, (169 / 200 : ℝ) ≤ u → u ≤ (677 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (667 / 5000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (169 / 200 : ℝ) (677 / 800 : ℝ) (5419479 / 1000000 : ℝ) (54330481921 / 10000000000 : ℝ)
    (20995169 / 12500000 : ℝ) (311 / 5000000000 : ℝ) (667 / 5000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (169 / 200 : ℝ)) (5419479 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (677 / 800 : ℝ) (233089 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (677 / 800 : ℝ))) h 2
    have he :
        (Real.exp (677 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (677 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (5419479 / 1000000 : ℝ) - (677 / 800 : ℝ) / 2) / 32)
      (20995169 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_677 :
    ∀ u : ℝ, (677 / 800 : ℝ) ≤ u → u ≤ (339 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (12849 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (677 / 800 : ℝ) (339 / 400 : ℝ) (1086609 / 200000 : ℝ) (1361662611409 / 250000000000 : ℝ)
    (840909 / 500000 : ℝ) (149 / 2500000000 : ℝ) (12849 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (677 / 800 : ℝ)) (1086609 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (339 / 400 : ℝ) (1166903 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (339 / 400 : ℝ))) h 2
    have he :
        (Real.exp (339 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (339 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1086609 / 200000 : ℝ) - (339 / 400 : ℝ) / 2) / 32)
      (840909 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_678 :
    ∀ u : ℝ, (339 / 400 : ℝ) ≤ u → u ≤ (679 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (12397 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (339 / 400 : ℝ) (679 / 800 : ℝ) (1361661 / 250000 : ℝ) (8736453961 / 1600000000 : ℝ)
    (168403083 / 100000000 : ℝ) (143 / 2500000000 : ℝ) (12397 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (339 / 400 : ℝ)) (1361661 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (679 / 800 : ℝ) (93469 / 40000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (679 / 800 : ℝ))) h 2
    have he :
        (Real.exp (679 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (679 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1361661 / 250000 : ℝ) - (679 / 800 : ℝ) / 2) / 32)
      (168403083 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_679 :
    ∀ u : ℝ, (679 / 800 : ℝ) ≤ u → u ≤ (17 / 20 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (11939 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (679 / 800 : ℝ) (17 / 20 : ℝ) (2730139 / 500000 : ℝ) (5473948084609 / 1000000000000 : ℝ)
    (42156309 / 25000000 : ℝ) (137 / 2500000000 : ℝ) (11939 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (679 / 800 : ℝ)) (2730139 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (17 / 20 : ℝ) (2339647 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (17 / 20 : ℝ))) h 2
    have he :
        (Real.exp (17 / 20 : ℝ)) ^ 2 =
          Real.exp (2 * (17 / 20 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2730139 / 500000 : ℝ) - (17 / 20 : ℝ) / 2) / 32)
      (42156309 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_660
#print axioms hpThetaEnergyUpper_interval_679

end HodgeProofHP
