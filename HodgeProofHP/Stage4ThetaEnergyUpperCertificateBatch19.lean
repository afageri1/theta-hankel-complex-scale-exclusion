import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_380 :
    ∀ u : ℝ, (19 / 40 : ℝ) ≤ u → u ≤ (381 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (16516247 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (19 / 40 : ℝ) (381 / 800 : ℝ) (2585709 / 1000000 : ℝ) (648045930169 / 250000000000 : ℝ)
    (7995371 / 6250000 : ℝ) (1889273 / 5000000000 : ℝ) (16516247 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (19 / 40 : ℝ)) (2585709 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (381 / 800 : ℝ) (805013 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (381 / 800 : ℝ))) h 2
    have he :
        (Real.exp (381 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (381 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2585709 / 1000000 : ℝ) - (381 / 800 : ℝ) / 2) / 32)
      (7995371 / 6250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_381 :
    ∀ u : ℝ, (381 / 800 : ℝ) ≤ u → u ≤ (191 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (101777 / 625000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (381 / 800 : ℝ) (191 / 400 : ℝ) (1296091 / 500000 : ℝ) (1624170601 / 625000000 : ℝ)
    (32001179 / 25000000 : ℝ) (926209 / 2500000000 : ℝ) (101777 / 625000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (381 / 800 : ℝ)) (1296091 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (191 / 400 : ℝ) (40301 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (191 / 400 : ℝ))) h 2
    have he :
        (Real.exp (191 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (191 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1296091 / 500000 : ℝ) - (191 / 400 : ℝ) / 2) / 32)
      (32001179 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_382 :
    ∀ u : ℝ, (191 / 400 : ℝ) ≤ u → u ≤ (383 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (16054849 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (191 / 400 : ℝ) (383 / 800 : ℝ) (259867 / 100000 : ℝ) (40705887049 / 15625000000 : ℝ)
    (32020933 / 25000000 : ℝ) (1816197 / 5000000000 : ℝ) (16054849 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (191 / 400 : ℝ)) (259867 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (383 / 800 : ℝ) (201757 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (383 / 800 : ℝ))) h 2
    have he :
        (Real.exp (383 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (383 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (259867 / 100000 : ℝ) - (383 / 800 : ℝ) / 2) / 32)
      (32020933 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_383 :
    ∀ u : ℝ, (383 / 800 : ℝ) ≤ u → u ≤ (12 / 25 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (3165551 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (383 / 800 : ℝ) (12 / 25 : ℝ) (104207 / 40000 : ℝ) (4178717449 / 1600000000 : ℝ)
    (128163011 / 100000000 : ℝ) (3561177 / 10000000000 : ℝ) (3165551 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (383 / 800 : ℝ)) (104207 / 40000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (12 / 25 : ℝ) (64643 / 40000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (12 / 25 : ℝ))) h 2
    have he :
        (Real.exp (12 / 25 : ℝ)) ^ 2 =
          Real.exp (2 * (12 / 25 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (104207 / 40000 : ℝ) - (12 / 25 : ℝ) / 2) / 32)
      (128163011 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_384 :
    ∀ u : ℝ, (12 / 25 : ℝ) ≤ u → u ≤ (77 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (15603039 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (12 / 25 : ℝ) (77 / 160 : ℝ) (163231 / 62500 : ℝ) (10227479161 / 3906250000 : ℝ)
    (128242541 / 100000000 : ℝ) (3491181 / 10000000000 : ℝ) (15603039 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (12 / 25 : ℝ)) (163231 / 62500 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (77 / 160 : ℝ) (101131 / 62500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (77 / 160 : ℝ))) h 2
    have he :
        (Real.exp (77 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (77 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (163231 / 62500 : ℝ) - (77 / 160 : ℝ) / 2) / 32)
      (128242541 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_385 :
    ∀ u : ℝ, (77 / 160 : ℝ) ≤ u → u ≤ (193 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (7690371 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (77 / 160 : ℝ) (193 / 400 : ℝ) (2618233 / 1000000 : ℝ) (1640493009 / 625000000 : ℝ)
    (128322321 / 100000000 : ℝ) (342239 / 1000000000 : ℝ) (7690371 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (77 / 160 : ℝ)) (2618233 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (193 / 400 : ℝ) (40503 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (193 / 400 : ℝ))) h 2
    have he :
        (Real.exp (193 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (193 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2618233 / 1000000 : ℝ) - (193 / 400 : ℝ) / 2) / 32)
      (128322321 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_386 :
    ∀ u : ℝ, (193 / 400 : ℝ) ≤ u → u ≤ (387 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1895099 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (193 / 400 : ℝ) (387 / 800 : ℝ) (2624787 / 1000000 : ℝ) (2631360889609 / 1000000000000 : ℝ)
    (25680473 / 20000000 : ℝ) (1677387 / 5000000000 : ℝ) (1895099 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (193 / 400 : ℝ)) (2624787 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (387 / 800 : ℝ) (1622147 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (387 / 800 : ℝ))) h 2
    have he :
        (Real.exp (387 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (387 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2624787 / 1000000 : ℝ) - (387 / 800 : ℝ) / 2) / 32)
      (25680473 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_387 :
    ∀ u : ℝ, (387 / 800 : ℝ) ≤ u → u ≤ (97 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (7471597 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (387 / 800 : ℝ) (97 / 200 : ℝ) (2631357 / 1000000 : ℝ) (10304483121 / 3906250000 : ℝ)
    (128482661 / 100000000 : ℝ) (328833 / 1000000000 : ℝ) (7471597 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (387 / 800 : ℝ)) (2631357 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (97 / 200 : ℝ) (101511 / 62500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (97 / 200 : ℝ))) h 2
    have he :
        (Real.exp (97 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (97 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2631357 / 1000000 : ℝ) - (97 / 200 : ℝ) / 2) / 32)
      (128482661 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_388 :
    ∀ u : ℝ, (97 / 200 : ℝ) ≤ u → u ≤ (389 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (117823 / 800000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (97 / 200 : ℝ) (389 / 800 : ℝ) (329743 / 125000 : ℝ) (2644549206849 / 1000000000000 : ℝ)
    (64281611 / 50000000 : ℝ) (805757 / 2500000000 : ℝ) (117823 / 800000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (97 / 200 : ℝ)) (329743 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (389 / 800 : ℝ) (1626207 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (389 / 800 : ℝ))) h 2
    have he :
        (Real.exp (389 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (389 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (329743 / 125000 : ℝ) - (389 / 800 : ℝ) / 2) / 32)
      (64281611 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_389 :
    ∀ u : ℝ, (389 / 800 : ℝ) ≤ u → u ≤ (39 / 80 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2902987 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (389 / 800 : ℝ) (39 / 80 : ℝ) (2644547 / 1000000 : ℝ) (2651168754081 / 1000000000000 : ℝ)
    (25728807 / 20000000 : ℝ) (1579433 / 5000000000 : ℝ) (2902987 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (389 / 800 : ℝ)) (2644547 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (39 / 80 : ℝ) (1628241 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (39 / 80 : ℝ))) h 2
    have he :
        (Real.exp (39 / 80 : ℝ)) ^ 2 =
          Real.exp (2 * (39 / 80 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2644547 / 1000000 : ℝ) - (39 / 80 : ℝ) / 2) / 32)
      (25728807 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_390 :
    ∀ u : ℝ, (39 / 80 : ℝ) ≤ u → u ≤ (391 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (143043 / 1000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (39 / 80 : ℝ) (391 / 800 : ℝ) (2651167 / 1000000 : ℝ) (664451589321 / 250000000000 : ℝ)
    (128725113 / 100000000 : ℝ) (619163 / 2000000000 : ℝ) (143043 / 1000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (39 / 80 : ℝ)) (2651167 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (391 / 800 : ℝ) (815139 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (391 / 800 : ℝ))) h 2
    have he :
        (Real.exp (391 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (391 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2651167 / 1000000 : ℝ) - (391 / 800 : ℝ) / 2) / 32)
      (128725113 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_391 :
    ∀ u : ℝ, (391 / 800 : ℝ) ≤ u → u ≤ (49 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (14095973 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (391 / 800 : ℝ) (49 / 100 : ℝ) (2657803 / 1000000 : ℝ) (2664458788489 / 1000000000000 : ℝ)
    (25761289 / 20000000 : ℝ) (3033871 / 10000000000 : ℝ) (14095973 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (391 / 800 : ℝ)) (2657803 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (49 / 100 : ℝ) (1632317 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (49 / 100 : ℝ))) h 2
    have he :
        (Real.exp (49 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (49 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2657803 / 1000000 : ℝ) - (49 / 100 : ℝ) / 2) / 32)
      (25761289 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_392 :
    ∀ u : ℝ, (49 / 100 : ℝ) ≤ u → u ≤ (393 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (434059 / 3125000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (49 / 100 : ℝ) (393 / 800 : ℝ) (333057 / 125000 : ℝ) (667781518041 / 250000000000 : ℝ)
    (128888043 / 100000000 : ℝ) (2973007 / 10000000000 : ℝ) (434059 / 3125000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (49 / 100 : ℝ)) (333057 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (393 / 800 : ℝ) (817179 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (393 / 800 : ℝ))) h 2
    have he :
        (Real.exp (393 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (393 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (333057 / 125000 : ℝ) - (393 / 800 : ℝ) / 2) / 32)
      (128888043 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_393 :
    ∀ u : ℝ, (393 / 800 : ℝ) ≤ u → u ≤ (197 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (13686163 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (393 / 800 : ℝ) (197 / 400 : ℝ) (21369 / 8000 : ℝ) (2677814778409 / 1000000000000 : ℝ)
    (16121237 / 12500000 : ℝ) (2913217 / 10000000000 : ℝ) (13686163 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (393 / 800 : ℝ)) (21369 / 8000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (197 / 400 : ℝ) (1636403 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (197 / 400 : ℝ))) h 2
    have he :
        (Real.exp (197 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (197 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (21369 / 8000 : ℝ) - (197 / 400 : ℝ) / 2) / 32)
      (16121237 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_394 :
    ∀ u : ℝ, (197 / 400 : ℝ) ≤ u → u ≤ (79 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (13484631 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (197 / 400 : ℝ) (79 / 160 : ℝ) (2677811 / 1000000 : ℝ) (2684515125601 / 1000000000000 : ℝ)
    (25810403 / 20000000 : ℝ) (2854479 / 10000000000 : ℝ) (13484631 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (197 / 400 : ℝ)) (2677811 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (79 / 160 : ℝ) (1638449 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (79 / 160 : ℝ))) h 2
    have he :
        (Real.exp (79 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (79 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2677811 / 1000000 : ℝ) - (79 / 160 : ℝ) / 2) / 32)
      (25810403 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_395 :
    ∀ u : ℝ, (79 / 160 : ℝ) ≤ u → u ≤ (99 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (6642691 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (79 / 160 : ℝ) (99 / 200 : ℝ) (1342257 / 500000 : ℝ) (2691236969001 / 1000000000000 : ℝ)
    (129134403 / 100000000 : ℝ) (1398387 / 5000000000 : ℝ) (6642691 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (79 / 160 : ℝ)) (1342257 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (99 / 200 : ℝ) (1640499 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (99 / 200 : ℝ))) h 2
    have he :
        (Real.exp (99 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (99 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1342257 / 500000 : ℝ) - (99 / 200 : ℝ) / 2) / 32)
      (129134403 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_396 :
    ∀ u : ℝ, (99 / 200 : ℝ) ≤ u → u ≤ (397 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1636043 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (99 / 200 : ℝ) (397 / 800 : ℝ) (1345617 / 500000 : ℝ) (2697973787601 / 1000000000000 : ℝ)
    (64608529 / 50000000 : ℝ) (2740091 / 10000000000 : ℝ) (1636043 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (99 / 200 : ℝ)) (1345617 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (397 / 800 : ℝ) (1642551 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (397 / 800 : ℝ))) h 2
    have he :
        (Real.exp (397 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (397 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1345617 / 500000 : ℝ) - (397 / 800 : ℝ) / 2) / 32)
      (64608529 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_397 :
    ∀ u : ℝ, (397 / 800 : ℝ) ≤ u → u ≤ (199 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1289353 / 10000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (397 / 800 : ℝ) (199 / 400 : ℝ) (269797 / 100000 : ℝ) (108189024241 / 40000000000 : ℝ)
    (12929997 / 10000000 : ℝ) (134221 / 500000000 : ℝ) (1289353 / 10000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (397 / 800 : ℝ)) (269797 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (199 / 400 : ℝ) (328921 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (199 / 400 : ℝ))) h 2
    have he :
        (Real.exp (199 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (199 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (269797 / 100000 : ℝ) - (199 / 400 : ℝ) / 2) / 32)
      (12929997 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_398 :
    ∀ u : ℝ, (199 / 400 : ℝ) ≤ u → u ≤ (399 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (12700899 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (199 / 400 : ℝ) (399 / 800 : ℝ) (676181 / 250000 : ℝ) (677873935561 / 250000000000 : ℝ)
    (129383163 / 100000000 : ℝ) (2629733 / 10000000000 : ℝ) (12700899 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (199 / 400 : ℝ)) (676181 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (399 / 800 : ℝ) (823331 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (399 / 800 : ℝ))) h 2
    have he :
        (Real.exp (399 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (399 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (676181 / 250000 : ℝ) - (399 / 800 : ℝ) / 2) / 32)
      (129383163 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_399 :
    ∀ u : ℝ, (399 / 800 : ℝ) ≤ u → u ≤ (1 / 2 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (781907 / 6250000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (399 / 800 : ℝ) (1 / 2 : ℝ) (1355747 / 500000 : ℝ) (679571058321 / 250000000000 : ℝ)
    (129466613 / 100000000 : ℝ) (257603 / 1000000000 : ℝ) (781907 / 6250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (399 / 800 : ℝ)) (1355747 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (1 / 2 : ℝ) (824361 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (1 / 2 : ℝ))) h 2
    have he :
        (Real.exp (1 / 2 : ℝ)) ^ 2 =
          Real.exp (2 * (1 / 2 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1355747 / 500000 : ℝ) - (1 / 2 : ℝ) / 2) / 32)
      (129466613 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_380
#print axioms hpThetaEnergyUpper_interval_399

end HodgeProofHP
