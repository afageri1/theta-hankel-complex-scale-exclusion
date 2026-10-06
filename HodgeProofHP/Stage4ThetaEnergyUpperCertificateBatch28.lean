import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_560 :
    ∀ u : ℝ, (7 / 10 : ℝ) ≤ u → u ≤ (561 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (487009 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (7 / 10 : ℝ) (561 / 800 : ℝ) (4055199 / 1000000 : ℝ) (15880284289 / 3906250000 : ℝ)
    (73624833 / 50000000 : ℝ) (8381 / 2000000000 : ℝ) (487009 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (7 / 10 : ℝ)) (4055199 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (561 / 800 : ℝ) (126017 / 62500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (561 / 800 : ℝ))) h 2
    have he :
        (Real.exp (561 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (561 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4055199 / 1000000 : ℝ) - (561 / 800 : ℝ) / 2) / 32)
      (73624833 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_561 :
    ∀ u : ℝ, (561 / 800 : ℝ) ≤ u → u ≤ (281 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (474551 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (561 / 800 : ℝ) (281 / 400 : ℝ) (81307 / 20000 : ℝ) (1018882303609 / 250000000000 : ℝ)
    (147393531 / 100000000 : ℝ) (5077 / 1250000000 : ℝ) (474551 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (561 / 800 : ℝ)) (81307 / 20000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (281 / 400 : ℝ) (1009397 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (281 / 400 : ℝ))) h 2
    have he :
        (Real.exp (281 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (281 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (81307 / 20000 : ℝ) - (281 / 400 : ℝ) / 2) / 32)
      (147393531 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_562 :
    ∀ u : ℝ, (281 / 400 : ℝ) ≤ u → u ≤ (563 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (14449 / 3125000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (281 / 400 : ℝ) (563 / 800 : ℝ) (2037763 / 500000 : ℝ) (4085730499761 / 1000000000000 : ℝ)
    (73768949 / 50000000 : ℝ) (39363 / 10000000000 : ℝ) (14449 / 3125000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (281 / 400 : ℝ)) (2037763 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (563 / 800 : ℝ) (2021319 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (563 / 800 : ℝ))) h 2
    have he :
        (Real.exp (563 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (563 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2037763 / 500000 : ℝ) - (563 / 800 : ℝ) / 2) / 32)
      (73768949 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_563 :
    ∀ u : ℝ, (563 / 800 : ℝ) ≤ u → u ≤ (141 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (225233 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (563 / 800 : ℝ) (141 / 200 : ℝ) (127679 / 31250 : ℝ) (4095956679409 / 1000000000000 : ℝ)
    (147682783 / 100000000 : ℝ) (19073 / 5000000000 : ℝ) (225233 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (563 / 800 : ℝ)) (127679 / 31250 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (141 / 200 : ℝ) (2023847 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (141 / 200 : ℝ))) h 2
    have he :
        (Real.exp (141 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (141 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (127679 / 31250 : ℝ) - (141 / 200 : ℝ) / 2) / 32)
      (147682783 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_564 :
    ∀ u : ℝ, (141 / 200 : ℝ) ≤ u → u ≤ (113 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (10971 / 2500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (141 / 200 : ℝ) (113 / 160 : ℝ) (819191 / 200000 : ℝ) (4106211851641 / 1000000000000 : ℝ)
    (73914087 / 50000000 : ℝ) (9241 / 2500000000 : ℝ) (10971 / 2500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (141 / 200 : ℝ)) (819191 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (113 / 160 : ℝ) (2026379 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (113 / 160 : ℝ))) h 2
    have he :
        (Real.exp (113 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (113 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (819191 / 200000 : ℝ) - (113 / 160 : ℝ) / 2) / 32)
      (73914087 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_565 :
    ∀ u : ℝ, (113 / 160 : ℝ) ≤ u → u ≤ (283 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (427469 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (113 / 160 : ℝ) (283 / 400 : ℝ) (4106207 / 1000000 : ℝ) (4116487961569 / 1000000000000 : ℝ)
    (14797407 / 10000000 : ℝ) (7163 / 2000000000 : ℝ) (427469 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (113 / 160 : ℝ)) (4106207 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (283 / 400 : ℝ) (2028913 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (283 / 400 : ℝ))) h 2
    have he :
        (Real.exp (283 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (283 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4106207 / 1000000 : ℝ) - (283 / 400 : ℝ) / 2) / 32)
      (14797407 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_566 :
    ∀ u : ℝ, (283 / 400 : ℝ) ≤ u → u ≤ (567 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (10409 / 2500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (283 / 400 : ℝ) (567 / 800 : ℝ) (2058243 / 500000 : ℝ) (4126793165401 / 1000000000000 : ℝ)
    (148120503 / 100000000 : ℝ) (34699 / 10000000000 : ℝ) (10409 / 2500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (283 / 400 : ℝ)) (2058243 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (567 / 800 : ℝ) (2031451 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (567 / 800 : ℝ))) h 2
    have he :
        (Real.exp (567 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (567 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2058243 / 500000 : ℝ) - (567 / 800 : ℝ) / 2) / 32)
      (148120503 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_567 :
    ∀ u : ℝ, (567 / 800 : ℝ) ≤ u → u ≤ (71 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (202759 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (567 / 800 : ℝ) (71 / 100 : ℝ) (412679 / 100000 : ℝ) (64642554001 / 15625000000 : ℝ)
    (29653489 / 20000000 : ℝ) (2101 / 625000000 : ℝ) (202759 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (567 / 800 : ℝ)) (412679 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (71 / 100 : ℝ) (254249 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (71 / 100 : ℝ))) h 2
    have he :
        (Real.exp (71 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (71 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (412679 / 100000 : ℝ) - (71 / 100 : ℝ) / 2) / 32)
      (29653489 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_568 :
    ∀ u : ℝ, (71 / 100 : ℝ) ≤ u → u ≤ (569 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (12341 / 3125000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (71 / 100 : ℝ) (569 / 800 : ℝ) (25857 / 6250 : ℝ) (64804357489 / 15625000000 : ℝ)
    (148414911 / 100000000 : ℝ) (32563 / 10000000000 : ℝ) (12341 / 3125000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (71 / 100 : ℝ)) (25857 / 6250 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (569 / 800 : ℝ) (254567 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (569 / 800 : ℝ))) h 2
    have he :
        (Real.exp (569 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (569 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (25857 / 6250 : ℝ) - (569 / 800 : ℝ) / 2) / 32)
      (148414911 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_569 :
    ∀ u : ℝ, (569 / 800 : ℝ) ≤ u → u ≤ (57 / 80 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (192279 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (569 / 800 : ℝ) (57 / 80 : ℝ) (1036869 / 250000 : ℝ) (4157859480889 / 1000000000000 : ℝ)
    (74281451 / 50000000 : ℝ) (31541 / 10000000000 : ℝ) (192279 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (569 / 800 : ℝ)) (1036869 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (57 / 80 : ℝ) (2039083 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (57 / 80 : ℝ))) h 2
    have he :
        (Real.exp (57 / 80 : ℝ)) ^ 2 =
          Real.exp (2 * (57 / 80 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1036869 / 250000 : ℝ) - (57 / 80 : ℝ) / 2) / 32)
      (74281451 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_570 :
    ∀ u : ℝ, (57 / 80 : ℝ) ≤ u → u ≤ (571 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (374451 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (57 / 80 : ℝ) (571 / 800 : ℝ) (4157857 / 1000000 : ℝ) (1042067347489 / 250000000000 : ℝ)
    (74355703 / 50000000 : ℝ) (30549 / 10000000000 : ℝ) (374451 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (57 / 80 : ℝ)) (4157857 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (571 / 800 : ℝ) (1020817 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (571 / 800 : ℝ))) h 2
    have he :
        (Real.exp (571 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (571 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4157857 / 1000000 : ℝ) - (571 / 800 : ℝ) / 2) / 32)
      (74355703 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_571 :
    ∀ u : ℝ, (571 / 800 : ℝ) ≤ u → u ≤ (143 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (364569 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (571 / 800 : ℝ) (143 / 200 : ℝ) (833653 / 200000 : ℝ) (4178700490969 / 1000000000000 : ℝ)
    (148860453 / 100000000 : ℝ) (5917 / 2000000000 : ℝ) (364569 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (571 / 800 : ℝ)) (833653 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (143 / 200 : ℝ) (2044187 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (143 / 200 : ℝ))) h 2
    have he :
        (Real.exp (143 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (143 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (833653 / 200000 : ℝ) - (143 / 200 : ℝ) / 2) / 32)
      (148860453 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_572 :
    ∀ u : ℝ, (143 / 200 : ℝ) ≤ u → u ≤ (573 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (354917 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (143 / 200 : ℝ) (573 / 800 : ℝ) (4178699 / 1000000 : ℝ) (65455640649 / 15625000000 : ℝ)
    (149010029 / 100000000 : ℝ) (28649 / 10000000000 : ℝ) (354917 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (143 / 200 : ℝ)) (4178699 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (573 / 800 : ℝ) (255843 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (573 / 800 : ℝ))) h 2
    have he :
        (Real.exp (573 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (573 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4178699 / 1000000 : ℝ) - (573 / 800 : ℝ) / 2) / 32)
      (149010029 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_573 :
    ∀ u : ℝ, (573 / 800 : ℝ) ≤ u → u ≤ (287 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (345501 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (573 / 800 : ℝ) (287 / 400 : ℝ) (2094579 / 500000 : ℝ) (65619482569 / 15625000000 : ℝ)
    (74580061 / 50000000 : ℝ) (27741 / 10000000000 : ℝ) (345501 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (573 / 800 : ℝ)) (2094579 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (287 / 400 : ℝ) (256163 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (287 / 400 : ℝ))) h 2
    have he :
        (Real.exp (287 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (287 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2094579 / 500000 : ℝ) - (287 / 400 : ℝ) / 2) / 32)
      (74580061 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_574 :
    ∀ u : ℝ, (287 / 400 : ℝ) ≤ u → u ≤ (23 / 32 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (3363 / 1000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (287 / 400 : ℝ) (23 / 32 : ℝ) (1049911 / 250000 : ℝ) (4210158185689 / 1000000000000 : ℝ)
    (149310761 / 100000000 : ℝ) (26859 / 10000000000 : ℝ) (3363 / 1000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (287 / 400 : ℝ)) (1049911 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (23 / 32 : ℝ) (2051867 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (23 / 32 : ℝ))) h 2
    have he :
        (Real.exp (23 / 32 : ℝ)) ^ 2 =
          Real.exp (2 * (23 / 32 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1049911 / 250000 : ℝ) - (23 / 32 : ℝ) / 2) / 32)
      (149310761 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_575 :
    ∀ u : ℝ, (23 / 32 : ℝ) ≤ u → u ≤ (18 / 25 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (163659 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (23 / 32 : ℝ) (18 / 25 : ℝ) (4210157 / 1000000 : ℝ) (1055174765089 / 250000000000 : ℝ)
    (149461949 / 100000000 : ℝ) (26003 / 10000000000 : ℝ) (163659 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (23 / 32 : ℝ)) (4210157 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (18 / 25 : ℝ) (1027217 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (18 / 25 : ℝ))) h 2
    have he :
        (Real.exp (18 / 25 : ℝ)) ^ 2 =
          Real.exp (2 * (18 / 25 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4210157 / 1000000 : ℝ) - (18 / 25 : ℝ) / 2) / 32)
      (149461949 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_576 :
    ∀ u : ℝ, (18 / 25 : ℝ) ≤ u → u ≤ (577 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (159279 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (18 / 25 : ℝ) (577 / 800 : ℝ) (844139 / 200000 : ℝ) (4231261342009 / 1000000000000 : ℝ)
    (149613657 / 100000000 : ℝ) (25173 / 10000000000 : ℝ) (159279 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (18 / 25 : ℝ)) (844139 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (577 / 800 : ℝ) (2057003 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (577 / 800 : ℝ))) h 2
    have he :
        (Real.exp (577 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (577 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (844139 / 200000 : ℝ) - (577 / 800 : ℝ) / 2) / 32)
      (149613657 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_577 :
    ∀ u : ℝ, (577 / 800 : ℝ) ≤ u → u ≤ (289 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (155001 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (577 / 800 : ℝ) (289 / 400 : ℝ) (211563 / 50000 : ℝ) (66278957809 / 15625000000 : ℝ)
    (29953183 / 20000000 : ℝ) (24367 / 10000000000 : ℝ) (155001 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (577 / 800 : ℝ)) (211563 / 50000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (289 / 400 : ℝ) (257447 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (289 / 400 : ℝ))) h 2
    have he :
        (Real.exp (289 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (289 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (211563 / 50000 : ℝ) - (289 / 400 : ℝ) / 2) / 32)
      (29953183 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_578 :
    ∀ u : ℝ, (289 / 400 : ℝ) ≤ u → u ≤ (579 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (301639 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (289 / 400 : ℝ) (579 / 800 : ℝ) (4241851 / 1000000 : ℝ) (66444857361 / 15625000000 : ℝ)
    (149918711 / 100000000 : ℝ) (737 / 312500000 : ℝ) (301639 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (289 / 400 : ℝ)) (4241851 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (579 / 800 : ℝ) (257769 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (579 / 800 : ℝ))) h 2
    have he :
        (Real.exp (579 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (579 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4241851 / 1000000 : ℝ) - (579 / 800 : ℝ) / 2) / 32)
      (149918711 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_579 :
    ∀ u : ℝ, (579 / 800 : ℝ) ≤ u → u ≤ (29 / 40 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (293487 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (579 / 800 : ℝ) (29 / 40 : ℝ) (4252469 / 1000000 : ℝ) (266444889489 / 62500000000 : ℝ)
    (7503603 / 5000000 : ℝ) (913 / 400000000 : ℝ) (293487 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (579 / 800 : ℝ)) (4252469 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (29 / 40 : ℝ) (516183 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (29 / 40 : ℝ))) h 2
    have he :
        (Real.exp (29 / 40 : ℝ)) ^ 2 =
          Real.exp (2 * (29 / 40 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4252469 / 1000000 : ℝ) - (29 / 40 : ℝ) / 2) / 32)
      (7503603 / 5000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_560
#print axioms hpThetaEnergyUpper_interval_579

end HodgeProofHP
