import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_320 :
    ∀ u : ℝ, (2 / 5 : ℝ) ≤ u → u ≤ (321 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (4399521 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (2 / 5 : ℝ) (321 / 800 : ℝ) (111277 / 50000 : ℝ) (2231112803481 / 1000000000000 : ℝ)
    (61814291 / 50000000 : ℝ) (11277053 / 10000000000 : ℝ) (4399521 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (2 / 5 : ℝ)) (111277 / 50000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (321 / 800 : ℝ) (1493691 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (321 / 800 : ℝ))) h 2
    have he :
        (Real.exp (321 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (321 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (111277 / 50000 : ℝ) - (321 / 800 : ℝ) / 2) / 32)
      (61814291 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_321 :
    ∀ u : ℝ, (321 / 800 : ℝ) ≤ u → u ≤ (161 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (34804287 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (321 / 800 : ℝ) (161 / 400 : ℝ) (2231111 / 1000000 : ℝ) (2236696722481 / 1000000000000 : ℝ)
    (123693767 / 100000000 : ℝ) (5544213 / 5000000000 : ℝ) (34804287 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (321 / 800 : ℝ)) (2231111 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (161 / 400 : ℝ) (1495559 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (161 / 400 : ℝ))) h 2
    have he :
        (Real.exp (161 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (161 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2231111 / 1000000 : ℝ) - (161 / 400 : ℝ) / 2) / 32)
      (123693767 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_322 :
    ∀ u : ℝ, (161 / 400 : ℝ) ≤ u → u ≤ (323 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (34415267 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (161 / 400 : ℝ) (323 / 800 : ℝ) (279587 / 125000 : ℝ) (22422966049 / 10000000000 : ℝ)
    (30939789 / 25000000 : ℝ) (10902477 / 10000000000 : ℝ) (34415267 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (161 / 400 : ℝ)) (279587 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (323 / 800 : ℝ) (149743 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (323 / 800 : ℝ))) h 2
    have he :
        (Real.exp (323 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (323 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (279587 / 125000 : ℝ) - (323 / 800 : ℝ) / 2) / 32)
      (30939789 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_323 :
    ∀ u : ℝ, (323 / 800 : ℝ) ≤ u → u ≤ (81 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (34028991 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (323 / 800 : ℝ) (81 / 200 : ℝ) (448459 / 200000 : ℝ) (2247909485809 / 1000000000000 : ℝ)
    (123824749 / 100000000 : ℝ) (1339897 / 1250000000 : ℝ) (34028991 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (323 / 800 : ℝ)) (448459 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (81 / 200 : ℝ) (1499303 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (81 / 200 : ℝ))) h 2
    have he :
        (Real.exp (81 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (81 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (448459 / 200000 : ℝ) - (81 / 200 : ℝ) / 2) / 32)
      (123824749 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_324 :
    ∀ u : ℝ, (81 / 200 : ℝ) ≤ u → u ≤ (13 / 32 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (16822781 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (81 / 200 : ℝ) (13 / 32 : ℝ) (2247907 / 1000000 : ℝ) (563383846921 / 250000000000 : ℝ)
    (15486317 / 12500000 : ℝ) (2634631 / 2500000000 : ℝ) (16822781 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (81 / 200 : ℝ)) (2247907 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (13 / 32 : ℝ) (750589 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (13 / 32 : ℝ))) h 2
    have he :
        (Real.exp (13 / 32 : ℝ)) ^ 2 =
          Real.exp (2 * (13 / 32 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2247907 / 1000000 : ℝ) - (13 / 32 : ℝ) / 2) / 32)
      (15486317 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_325 :
    ∀ u : ℝ, (13 / 32 : ℝ) ≤ u → u ≤ (163 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (33264891 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (13 / 32 : ℝ) (163 / 400 : ℝ) (1126767 / 500000 : ℝ) (8824911481 / 3906250000 : ℝ)
    (6197827 / 5000000 : ℝ) (1036043 / 1000000000 : ℝ) (33264891 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (13 / 32 : ℝ)) (1126767 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (163 / 400 : ℝ) (93941 / 62500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (163 / 400 : ℝ))) h 2
    have he :
        (Real.exp (163 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (163 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1126767 / 500000 : ℝ) - (163 / 400 : ℝ) / 2) / 32)
      (6197827 / 5000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_326 :
    ∀ u : ℝ, (163 / 400 : ℝ) ≤ u → u ≤ (327 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (16443489 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (163 / 400 : ℝ) (327 / 800 : ℝ) (90367 / 40000 : ℝ) (35388005689 / 15625000000 : ℝ)
    (124022749 / 100000000 : ℝ) (10184899 / 10000000000 : ℝ) (16443489 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (163 / 400 : ℝ)) (90367 / 40000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (327 / 800 : ℝ) (188117 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (327 / 800 : ℝ))) h 2
    have he :
        (Real.exp (327 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (327 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (90367 / 40000 : ℝ) - (327 / 800 : ℝ) / 2) / 32)
      (124022749 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_327 :
    ∀ u : ℝ, (327 / 800 : ℝ) ≤ u → u ≤ (41 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (32511821 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (327 / 800 : ℝ) (41 / 100 : ℝ) (226483 / 100000 : ℝ) (567625121281 / 250000000000 : ℝ)
    (31022291 / 25000000 : ℝ) (10011901 / 10000000000 : ℝ) (32511821 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (327 / 800 : ℝ)) (226483 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (41 / 100 : ℝ) (753409 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (41 / 100 : ℝ))) h 2
    have he :
        (Real.exp (41 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (41 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (226483 / 100000 : ℝ) - (41 / 100 : ℝ) / 2) / 32)
      (31022291 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_328 :
    ∀ u : ℝ, (41 / 100 : ℝ) ≤ u → u ≤ (329 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (32139527 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (41 / 100 : ℝ) (329 / 800 : ℝ) (2270499 / 1000000 : ℝ) (2276184742209 / 1000000000000 : ℝ)
    (62077893 / 50000000 : ℝ) (9841407 / 10000000000 : ℝ) (32139527 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (41 / 100 : ℝ)) (2270499 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (329 / 800 : ℝ) (1508703 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (329 / 800 : ℝ))) h 2
    have he :
        (Real.exp (329 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (329 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2270499 / 1000000 : ℝ) - (329 / 800 : ℝ) / 2) / 32)
      (62077893 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_329 :
    ∀ u : ℝ, (329 / 800 : ℝ) ≤ u → u ≤ (33 / 80 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (15884949 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (329 / 800 : ℝ) (33 / 80 : ℝ) (2276183 / 1000000 : ℝ) (22818821481 / 10000000000 : ℝ)
    (62111313 / 50000000 : ℝ) (4836681 / 5000000000 : ℝ) (15884949 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (329 / 800 : ℝ)) (2276183 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (33 / 80 : ℝ) (151059 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (33 / 80 : ℝ))) h 2
    have he :
        (Real.exp (33 / 80 : ℝ)) ^ 2 =
          Real.exp (2 * (33 / 80 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2276183 / 1000000 : ℝ) - (33 / 80 : ℝ) / 2) / 32)
      (62111313 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_330 :
    ∀ u : ℝ, (33 / 80 : ℝ) ≤ u → u ≤ (331 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (6280629 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (33 / 80 : ℝ) (331 / 800 : ℝ) (57047 / 25000 : ℝ) (2287592725441 / 1000000000000 : ℝ)
    (6214483 / 5000000 : ℝ) (47539 / 50000000 : ℝ) (6280629 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (33 / 80 : ℝ)) (57047 / 25000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (331 / 800 : ℝ) (1512479 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (331 / 800 : ℝ))) h 2
    have he :
        (Real.exp (331 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (331 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (57047 / 25000 : ℝ) - (331 / 800 : ℝ) / 2) / 32)
      (6214483 / 5000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_331 :
    ∀ u : ℝ, (331 / 800 : ℝ) ≤ u → u ≤ (83 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (6207831 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (331 / 800 : ℝ) (83 / 200 : ℝ) (285949 / 125000 : ℝ) (2293319525641 / 1000000000000 : ℝ)
    (62178457 / 50000000 : ℝ) (9344629 / 10000000000 : ℝ) (6207831 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (331 / 800 : ℝ)) (285949 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (83 / 200 : ℝ) (1514371 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (83 / 200 : ℝ))) h 2
    have he :
        (Real.exp (83 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (83 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (285949 / 125000 : ℝ) - (83 / 200 : ℝ) / 2) / 32)
      (62178457 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_332 :
    ∀ u : ℝ, (83 / 200 : ℝ) ≤ u → u ≤ (333 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (30677941 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (83 / 200 : ℝ) (333 / 800 : ℝ) (1146659 / 500000 : ℝ) (91962382009 / 40000000000 : ℝ)
    (199079 / 160000 : ℝ) (573991 / 625000000 : ℝ) (30677941 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (83 / 200 : ℝ)) (1146659 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (333 / 800 : ℝ) (303253 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (333 / 800 : ℝ))) h 2
    have he :
        (Real.exp (333 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (333 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1146659 / 500000 : ℝ) - (333 / 800 : ℝ) / 2) / 32)
      (199079 / 160000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_333 :
    ∀ u : ℝ, (333 / 800 : ℝ) ≤ u → u ≤ (167 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (15159749 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (333 / 800 : ℝ) (167 / 400 : ℝ) (2299059 / 1000000 : ℝ) (576203964561 / 250000000000 : ℝ)
    (15561507 / 12500000 : ℝ) (9025423 / 10000000000 : ℝ) (15159749 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (333 / 800 : ℝ)) (2299059 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (167 / 400 : ℝ) (759081 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (167 / 400 : ℝ))) h 2
    have he :
        (Real.exp (167 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (167 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2299059 / 1000000 : ℝ) - (167 / 400 : ℝ) / 2) / 32)
      (15561507 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_334 :
    ∀ u : ℝ, (167 / 400 : ℝ) ≤ u → u ≤ (67 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (29963829 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (167 / 400 : ℝ) (67 / 160 : ℝ) (1152407 / 500000 : ℝ) (2310585443721 / 1000000000000 : ℝ)
    (24911989 / 20000000 : ℝ) (8869333 / 10000000000 : ℝ) (29963829 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (167 / 400 : ℝ)) (1152407 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (67 / 160 : ℝ) (1520061 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (67 / 160 : ℝ))) h 2
    have he :
        (Real.exp (67 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (67 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1152407 / 500000 : ℝ) - (67 / 160 : ℝ) / 2) / 32)
      (24911989 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_335 :
    ∀ u : ℝ, (67 / 160 : ℝ) ≤ u → u ≤ (21 / 50 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (29610937 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (67 / 160 : ℝ) (21 / 50 : ℝ) (2310583 / 1000000 : ℝ) (579092082361 / 250000000000 : ℝ)
    (62314021 / 50000000 : ℝ) (217889 / 250000000 : ℝ) (29610937 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (67 / 160 : ℝ)) (2310583 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (21 / 50 : ℝ) (760981 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (21 / 50 : ℝ))) h 2
    have he :
        (Real.exp (21 / 50 : ℝ)) ^ 2 =
          Real.exp (2 * (21 / 50 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2310583 / 1000000 : ℝ) - (21 / 50 : ℝ) / 2) / 32)
      (62314021 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_336 :
    ∀ u : ℝ, (21 / 50 : ℝ) ≤ u → u ≤ (337 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (5852183 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (21 / 50 : ℝ) (337 / 800 : ℝ) (1158183 / 500000 : ℝ) (580541896489 / 250000000000 : ℝ)
    (31174087 / 25000000 : ℝ) (2141019 / 2500000000 : ℝ) (5852183 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (21 / 50 : ℝ)) (1158183 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (337 / 800 : ℝ) (761933 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (337 / 800 : ℝ))) h 2
    have he :
        (Real.exp (337 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (337 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1158183 / 500000 : ℝ) - (337 / 800 : ℝ) / 2) / 32)
      (31174087 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_337 :
    ∀ u : ℝ, (337 / 800 : ℝ) ≤ u → u ≤ (169 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (14456741 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (337 / 800 : ℝ) (169 / 400 : ℝ) (464433 / 200000 : ℝ) (145498762249 / 62500000000 : ℝ)
    (124764887 / 100000000 : ℝ) (8414803 / 10000000000 : ℝ) (14456741 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (337 / 800 : ℝ)) (464433 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (169 / 400 : ℝ) (381443 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (169 / 400 : ℝ))) h 2
    have he :
        (Real.exp (169 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (169 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (464433 / 200000 : ℝ) - (169 / 400 : ℝ) / 2) / 32)
      (124764887 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_338 :
    ∀ u : ℝ, (169 / 400 : ℝ) ≤ u → u ≤ (339 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (14284459 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (169 / 400 : ℝ) (339 / 800 : ℝ) (2327977 / 1000000 : ℝ) (22791076 / 9765625 : ℝ)
    (124833623 / 100000000 : ℝ) (4133897 / 5000000000 : ℝ) (14284459 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (169 / 400 : ℝ)) (2327977 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (339 / 800 : ℝ) (4774 / 3125 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (339 / 800 : ℝ))) h 2
    have he :
        (Real.exp (339 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (339 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2327977 / 1000000 : ℝ) - (339 / 800 : ℝ) / 2) / 32)
      (124833623 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_339 :
    ∀ u : ℝ, (339 / 800 : ℝ) ≤ u → u ≤ (17 / 40 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (7056761 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (339 / 800 : ℝ) (17 / 40 : ℝ) (466761 / 200000 : ℝ) (2339648627281 / 1000000000000 : ℝ)
    (1951603 / 1562500 : ℝ) (8122947 / 10000000000 : ℝ) (7056761 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (339 / 800 : ℝ)) (466761 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (17 / 40 : ℝ) (1529591 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (17 / 40 : ℝ))) h 2
    have he :
        (Real.exp (17 / 40 : ℝ)) ^ 2 =
          Real.exp (2 * (17 / 40 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (466761 / 200000 : ℝ) - (17 / 40 : ℝ) / 2) / 32)
      (1951603 / 1562500 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_320
#print axioms hpThetaEnergyUpper_interval_339

end HodgeProofHP
