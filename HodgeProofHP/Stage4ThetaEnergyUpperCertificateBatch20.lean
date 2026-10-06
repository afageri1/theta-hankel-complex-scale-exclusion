import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_400 :
    ∀ u : ℝ, (1 / 2 : ℝ) ≤ u → u ≤ (401 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (12322279 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (1 / 2 : ℝ) (401 / 800 : ℝ) (2718281 / 1000000 : ℝ) (2661218569 / 976562500 : ℝ)
    (129550333 / 100000000 : ℝ) (2523289 / 10000000000 : ℝ) (12322279 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (1 / 2 : ℝ)) (2718281 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (401 / 800 : ℝ) (51587 / 31250 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (401 / 800 : ℝ))) h 2
    have he :
        (Real.exp (401 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (401 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2718281 / 1000000 : ℝ) - (401 / 800 : ℝ) / 2) / 32)
      (129550333 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_401 :
    ∀ u : ℝ, (401 / 800 : ℝ) ≤ u → u ≤ (201 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (3034047 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (401 / 800 : ℝ) (201 / 400 : ℝ) (1362543 / 500000 : ℝ) (2731909816801 / 1000000000000 : ℝ)
    (4051073 / 3125000 : ℝ) (38617 / 156250000 : ℝ) (3034047 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (401 / 800 : ℝ)) (1362543 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (201 / 400 : ℝ) (1652849 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (201 / 400 : ℝ))) h 2
    have he :
        (Real.exp (201 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (201 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1362543 / 500000 : ℝ) - (201 / 400 : ℝ) / 2) / 32)
      (4051073 / 3125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_402 :
    ∀ u : ℝ, (201 / 400 : ℝ) ≤ u → u ≤ (403 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2988067 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (201 / 400 : ℝ) (403 / 800 : ℝ) (2731907 / 1000000 : ℝ) (171171685441 / 62500000000 : ℝ)
    (129718597 / 100000000 : ℝ) (2420629 / 10000000000 : ℝ) (2988067 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (201 / 400 : ℝ)) (2731907 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (403 / 800 : ℝ) (413729 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (403 / 800 : ℝ))) h 2
    have he :
        (Real.exp (403 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (403 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2731907 / 1000000 : ℝ) - (403 / 800 : ℝ) / 2) / 32)
      (129718597 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_403 :
    ∀ u : ℝ, (403 / 800 : ℝ) ≤ u → u ≤ (101 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2942627 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (403 / 800 : ℝ) (101 / 200 : ℝ) (547749 / 200000 : ℝ) (686400651049 / 250000000000 : ℝ)
    (129803129 / 100000000 : ℝ) (2370691 / 10000000000 : ℝ) (2942627 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (403 / 800 : ℝ)) (547749 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (101 / 200 : ℝ) (828493 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (101 / 200 : ℝ))) h 2
    have he :
        (Real.exp (101 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (101 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (547749 / 200000 : ℝ) - (101 / 200 : ℝ) / 2) / 32)
      (129803129 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_404 :
    ∀ u : ℝ, (101 / 200 : ℝ) ≤ u → u ≤ (81 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (11590847 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (101 / 200 : ℝ) (81 / 160 : ℝ) (2745601 / 1000000 : ℝ) (2752476765481 / 1000000000000 : ℝ)
    (64943973 / 50000000 : ℝ) (2321651 / 10000000000 : ℝ) (11590847 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (101 / 200 : ℝ)) (2745601 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (81 / 160 : ℝ) (1659059 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (81 / 160 : ℝ))) h 2
    have he :
        (Real.exp (81 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (81 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2745601 / 1000000 : ℝ) - (81 / 160 : ℝ) / 2) / 32)
      (64943973 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_405 :
    ∀ u : ℝ, (81 / 160 : ℝ) ≤ u → u ≤ (203 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (5706661 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (81 / 160 : ℝ) (203 / 400 : ℝ) (2752473 / 1000000 : ℝ) (689841541489 / 250000000000 : ℝ)
    (64986511 / 50000000 : ℝ) (284189 / 1250000000 : ℝ) (5706661 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (81 / 160 : ℝ)) (2752473 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (203 / 400 : ℝ) (830567 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (203 / 400 : ℝ))) h 2
    have he :
        (Real.exp (203 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (203 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2752473 / 1000000 : ℝ) - (203 / 400 : ℝ) / 2) / 32)
      (64986511 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_406 :
    ∀ u : ℝ, (203 / 400 : ℝ) ≤ u → u ≤ (407 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2809459 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (203 / 400 : ℝ) (407 / 800 : ℝ) (2759363 / 1000000 : ℝ) (2766270830521 / 1000000000000 : ℝ)
    (8128649 / 6250000 : ℝ) (556561 / 2500000000 : ℝ) (2809459 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (203 / 400 : ℝ)) (2759363 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (407 / 800 : ℝ) (1663211 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (407 / 800 : ℝ))) h 2
    have he :
        (Real.exp (407 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (407 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2759363 / 1000000 : ℝ) - (407 / 800 : ℝ) / 2) / 32)
      (8128649 / 6250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_407 :
    ∀ u : ℝ, (407 / 800 : ℝ) ≤ u → u ≤ (51 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (11064489 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (407 / 800 : ℝ) (51 / 100 : ℝ) (276627 / 100000 : ℝ) (173324840329 / 62500000000 : ℝ)
    (130144019 / 100000000 : ℝ) (2179843 / 10000000000 : ℝ) (11064489 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (407 / 800 : ℝ)) (276627 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (51 / 100 : ℝ) (416323 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (51 / 100 : ℝ))) h 2
    have he :
        (Real.exp (51 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (51 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (276627 / 100000 : ℝ) - (51 / 100 : ℝ) / 2) / 32)
      (130144019 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_408 :
    ∀ u : ℝ, (51 / 100 : ℝ) ≤ u → u ≤ (409 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (5446599 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (51 / 100 : ℝ) (409 / 800 : ℝ) (1386597 / 500000 : ℝ) (177928921 / 64000000 : ℝ)
    (16278741 / 12500000 : ℝ) (426859 / 2000000000 : ℝ) (5446599 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (51 / 100 : ℝ)) (1386597 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (409 / 800 : ℝ) (13339 / 8000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (409 / 800 : ℝ))) h 2
    have he :
        (Real.exp (409 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (409 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1386597 / 500000 : ℝ) - (409 / 800 : ℝ) / 2) / 32)
      (16278741 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_409 :
    ∀ u : ℝ, (409 / 800 : ℝ) ≤ u → u ≤ (41 / 80 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (5361959 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (409 / 800 : ℝ) (41 / 80 : ℝ) (347517 / 125000 : ℝ) (6967741729 / 2500000000 : ℝ)
    (130316123 / 100000000 : ℝ) (2089581 / 10000000000 : ℝ) (5361959 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (409 / 800 : ℝ)) (347517 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (41 / 80 : ℝ) (83473 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (41 / 80 : ℝ))) h 2
    have he :
        (Real.exp (41 / 80 : ℝ)) ^ 2 =
          Real.exp (2 * (41 / 80 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (347517 / 125000 : ℝ) - (41 / 80 : ℝ) / 2) / 32)
      (130316123 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_410 :
    ∀ u : ℝ, (41 / 80 : ℝ) ≤ u → u ≤ (411 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (329897 / 3125000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (41 / 80 : ℝ) (411 / 800 : ℝ) (557419 / 200000 : ℝ) (174629544769 / 62500000000 : ℝ)
    (130402593 / 100000000 : ℝ) (409139 / 2000000000 : ℝ) (329897 / 3125000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (41 / 80 : ℝ)) (557419 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (411 / 800 : ℝ) (417887 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (411 / 800 : ℝ))) h 2
    have he :
        (Real.exp (411 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (411 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (557419 / 200000 : ℝ) - (411 / 800 : ℝ) / 2) / 32)
      (130402593 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_411 :
    ∀ u : ℝ, (411 / 800 : ℝ) ≤ u → u ≤ (103 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2078307 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (411 / 800 : ℝ) (103 / 200 : ℝ) (2794071 / 1000000 : ℝ) (2801067502321 / 1000000000000 : ℝ)
    (65244669 / 50000000 : ℝ) (2002623 / 10000000000 : ℝ) (2078307 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (411 / 800 : ℝ)) (2794071 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (103 / 200 : ℝ) (1673639 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (103 / 200 : ℝ))) h 2
    have he :
        (Real.exp (103 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (103 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2794071 / 1000000 : ℝ) - (103 / 200 : ℝ) / 2) / 32)
      (65244669 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_412 :
    ∀ u : ℝ, (103 / 200 : ℝ) ≤ u → u ≤ (413 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (639271 / 6250000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (103 / 200 : ℝ) (413 / 800 : ℝ) (560213 / 200000 : ℝ) (175504858489 / 62500000000 : ℝ)
    (32644093 / 25000000 : ℝ) (1960347 / 10000000000 : ℝ) (639271 / 6250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (103 / 200 : ℝ)) (560213 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (413 / 800 : ℝ) (418933 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (413 / 800 : ℝ))) h 2
    have he :
        (Real.exp (413 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (413 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (560213 / 200000 : ℝ) - (413 / 800 : ℝ) / 2) / 32)
      (32644093 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_413 :
    ∀ u : ℝ, (413 / 800 : ℝ) ≤ u → u ≤ (207 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (10067133 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (413 / 800 : ℝ) (207 / 400 : ℝ) (2808077 / 1000000 : ℝ) (175944174849 / 62500000000 : ℝ)
    (65331847 / 50000000 : ℝ) (239857 / 1250000000 : ℝ) (10067133 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (413 / 800 : ℝ)) (2808077 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (207 / 400 : ℝ) (419457 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (207 / 400 : ℝ))) h 2
    have he :
        (Real.exp (207 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (207 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2808077 / 1000000 : ℝ) - (207 / 400 : ℝ) / 2) / 32)
      (65331847 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_414 :
    ∀ u : ℝ, (207 / 400 : ℝ) ≤ u → u ≤ (83 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2476983 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (207 / 400 : ℝ) (83 / 160 : ℝ) (1407553 / 500000 : ℝ) (2822154725329 / 1000000000000 : ℝ)
    (130751293 / 100000000 : ℝ) (939071 / 5000000000 : ℝ) (2476983 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (207 / 400 : ℝ)) (1407553 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (83 / 160 : ℝ) (1679927 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (83 / 160 : ℝ))) h 2
    have he :
        (Real.exp (83 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (83 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1407553 / 500000 : ℝ) - (83 / 160 : ℝ) / 2) / 32)
      (130751293 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_415 :
    ∀ u : ℝ, (83 / 160 : ℝ) ≤ u → u ≤ (13 / 25 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (4875349 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (83 / 160 : ℝ) (13 / 25 : ℝ) (352769 / 125000 : ℝ) (176826137049 / 62500000000 : ℝ)
    (1022181 / 781250 : ℝ) (919097 / 5000000000 : ℝ) (4875349 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (83 / 160 : ℝ)) (352769 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (13 / 25 : ℝ) (420507 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (13 / 25 : ℝ))) h 2
    have he :
        (Real.exp (13 / 25 : ℝ)) ^ 2 =
          Real.exp (2 * (13 / 25 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (352769 / 125000 : ℝ) - (13 / 25 : ℝ) / 2) / 32)
      (1022181 / 781250 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_416 :
    ∀ u : ℝ, (13 / 25 : ℝ) ≤ u → u ≤ (417 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (479769 / 5000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (13 / 25 : ℝ) (417 / 800 : ℝ) (2829217 / 1000000 : ℝ) (177268787089 / 62500000000 : ℝ)
    (130927347 / 100000000 : ℝ) (449747 / 2500000000 : ℝ) (479769 / 5000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (13 / 25 : ℝ)) (2829217 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (417 / 800 : ℝ) (421033 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (417 / 800 : ℝ))) h 2
    have he :
        (Real.exp (417 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (417 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2829217 / 1000000 : ℝ) - (417 / 800 : ℝ) / 2) / 32)
      (130927347 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_417 :
    ∀ u : ℝ, (417 / 800 : ℝ) ≤ u → u ≤ (209 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (590127 / 6250000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (417 / 800 : ℝ) (209 / 400 : ℝ) (1418149 / 500000 : ℝ) (710849648161 / 250000000000 : ℝ)
    (131015791 / 100000000 : ℝ) (176053 / 1000000000 : ℝ) (590127 / 6250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (417 / 800 : ℝ)) (1418149 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (209 / 400 : ℝ) (843119 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (209 / 400 : ℝ))) h 2
    have he :
        (Real.exp (209 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (209 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1418149 / 500000 : ℝ) - (209 / 400 : ℝ) / 2) / 32)
      (131015791 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_418 :
    ∀ u : ℝ, (209 / 400 : ℝ) ≤ u → u ≤ (419 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (4645303 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (209 / 400 : ℝ) (419 / 800 : ℝ) (1421699 / 500000 : ℝ) (178157435569 / 62500000000 : ℝ)
    (6555227 / 5000000 : ℝ) (215349 / 1250000000 : ℝ) (4645303 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (209 / 400 : ℝ)) (1421699 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (419 / 800 : ℝ) (422087 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (419 / 800 : ℝ))) h 2
    have he :
        (Real.exp (419 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (419 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1421699 / 500000 : ℝ) - (419 / 800 : ℝ) / 2) / 32)
      (6555227 / 5000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_419 :
    ∀ u : ℝ, (419 / 800 : ℝ) ≤ u → u ≤ (21 / 40 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (457053 / 5000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (419 / 800 : ℝ) (21 / 40 : ℝ) (570103 / 200000 : ℝ) (2857651630681 / 1000000000000 : ℝ)
    (131193567 / 100000000 : ℝ) (421443 / 2500000000 : ℝ) (457053 / 5000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (419 / 800 : ℝ)) (570103 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (21 / 40 : ℝ) (1690459 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (21 / 40 : ℝ))) h 2
    have he :
        (Real.exp (21 / 40 : ℝ)) ^ 2 =
          Real.exp (2 * (21 / 40 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (570103 / 200000 : ℝ) - (21 / 40 : ℝ) / 2) / 32)
      (131193567 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_400
#print axioms hpThetaEnergyUpper_interval_419

end HodgeProofHP
