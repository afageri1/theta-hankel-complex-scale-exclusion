import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_760 :
    ∀ u : ℝ, (19 / 20 : ℝ) ≤ u → u ≤ (761 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (27 / 6250000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (19 / 20 : ℝ) (761 / 800 : ℝ) (6685889 / 1000000 : ℝ) (26182152481 / 3906250000 : ℝ)
    (189873823 / 100000000 : ℝ) (13 / 10000000000 : ℝ) (27 / 6250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (19 / 20 : ℝ)) (6685889 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (761 / 800 : ℝ) (161809 / 62500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (761 / 800 : ℝ))) h 2
    have he :
        (Real.exp (761 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (761 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (6685889 / 1000000 : ℝ) - (761 / 800 : ℝ) / 2) / 32)
      (189873823 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_761 :
    ∀ u : ℝ, (761 / 800 : ℝ) ≤ u → u ≤ (381 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (401 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (761 / 800 : ℝ) (381 / 400 : ℝ) (209457 / 31250 : ℝ) (6719412705489 / 1000000000000 : ℝ)
    (2377277 / 1250000 : ℝ) (3 / 2500000000 : ℝ) (401 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (761 / 800 : ℝ)) (209457 / 31250 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (381 / 400 : ℝ) (2592183 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (381 / 400 : ℝ))) h 2
    have he :
        (Real.exp (381 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (381 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (209457 / 31250 : ℝ) - (381 / 400 : ℝ) / 2) / 32)
      (2377277 / 1250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_762 :
    ∀ u : ℝ, (381 / 400 : ℝ) ≤ u → u ≤ (763 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (403 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (381 / 400 : ℝ) (763 / 800 : ℝ) (3359701 / 500000 : ℝ) (10777969489 / 1600000000 : ℝ)
    (95245901 / 50000000 : ℝ) (3 / 2500000000 : ℝ) (403 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (381 / 400 : ℝ)) (3359701 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (763 / 800 : ℝ) (103817 / 40000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (763 / 800 : ℝ))) h 2
    have he :
        (Real.exp (763 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (763 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3359701 / 500000 : ℝ) - (763 / 800 : ℝ) / 2) / 32)
      (95245901 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_763 :
    ∀ u : ℝ, (763 / 800 : ℝ) ≤ u → u ≤ (191 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (93 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (763 / 800 : ℝ) (191 / 200 : ℝ) (6736221 / 1000000 : ℝ) (6753090966241 / 1000000000000 : ℝ)
    (47700679 / 25000000 : ℝ) (11 / 10000000000 : ℝ) (93 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (763 / 800 : ℝ)) (6736221 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (191 / 200 : ℝ) (2598671 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (191 / 200 : ℝ))) h 2
    have he :
        (Real.exp (191 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (191 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (6736221 / 1000000 : ℝ) - (191 / 200 : ℝ) / 2) / 32)
      (47700679 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_764 :
    ∀ u : ℝ, (191 / 200 : ℝ) ≤ u → u ≤ (153 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (17 / 5000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (191 / 200 : ℝ) (153 / 160 : ℝ) (6753083 / 1000000 : ℝ) (6769992890241 / 1000000000000 : ℝ)
    (2986171 / 1562500 : ℝ) (1 / 1000000000 : ℝ) (17 / 5000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (191 / 200 : ℝ)) (6753083 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (153 / 160 : ℝ) (2601921 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (153 / 160 : ℝ))) h 2
    have he :
        (Real.exp (153 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (153 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (6753083 / 1000000 : ℝ) - (153 / 160 : ℝ) / 2) / 32)
      (2986171 / 1562500 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_765 :
    ∀ u : ℝ, (153 / 160 : ℝ) ≤ u → u ≤ (383 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (171 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (153 / 160 : ℝ) (383 / 400 : ℝ) (3384993 / 500000 : ℝ) (106045968609 / 15625000000 : ℝ)
    (47857113 / 25000000 : ℝ) (1 / 1000000000 : ℝ) (171 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (153 / 160 : ℝ)) (3384993 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (383 / 400 : ℝ) (325647 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (383 / 400 : ℝ))) h 2
    have he :
        (Real.exp (383 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (383 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3384993 / 500000 : ℝ) - (383 / 400 : ℝ) / 2) / 32)
      (47857113 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_766 :
    ∀ u : ℝ, (383 / 400 : ℝ) ≤ u → u ≤ (767 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (309 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (383 / 400 : ℝ) (767 / 800 : ℝ) (1696733 / 250000 : ℝ) (1700981983089 / 250000000000 : ℝ)
    (47935821 / 25000000 : ℝ) (9 / 10000000000 : ℝ) (309 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (383 / 400 : ℝ)) (1696733 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (767 / 800 : ℝ) (1304217 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (767 / 800 : ℝ))) h 2
    have he :
        (Real.exp (767 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (767 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1696733 / 250000 : ℝ) - (767 / 800 : ℝ) / 2) / 32)
      (47935821 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_767 :
    ∀ u : ℝ, (767 / 800 : ℝ) ≤ u → u ≤ (24 / 25 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (311 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (767 / 800 : ℝ) (24 / 25 : ℝ) (6803921 / 1000000 : ℝ) (6820961219809 / 1000000000000 : ℝ)
    (38411889 / 20000000 : ℝ) (9 / 10000000000 : ℝ) (311 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (767 / 800 : ℝ)) (6803921 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (24 / 25 : ℝ) (2611697 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (24 / 25 : ℝ))) h 2
    have he :
        (Real.exp (24 / 25 : ℝ)) ^ 2 =
          Real.exp (2 * (24 / 25 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (6803921 / 1000000 : ℝ) - (24 / 25 : ℝ) / 2) / 32)
      (38411889 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_768 :
    ∀ u : ℝ, (24 / 25 : ℝ) ≤ u → u ≤ (769 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (39 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (24 / 25 : ℝ) (769 / 800 : ℝ) (852619 / 125000 : ℝ) (427377295081 / 62500000000 : ℝ)
    (192376919 / 100000000 : ℝ) (9 / 10000000000 : ℝ) (39 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (24 / 25 : ℝ)) (852619 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (769 / 800 : ℝ) (653741 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (769 / 800 : ℝ))) h 2
    have he :
        (Real.exp (769 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (769 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (852619 / 125000 : ℝ) - (769 / 800 : ℝ) / 2) / 32)
      (192376919 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_769 :
    ∀ u : ℝ, (769 / 800 : ℝ) ≤ u → u ≤ (77 / 80 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (279 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (769 / 800 : ℝ) (77 / 80 : ℝ) (273521 / 40000 : ℝ) (1713787319689 / 250000000000 : ℝ)
    (6021741 / 3125000 : ℝ) (1 / 1250000000 : ℝ) (279 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (769 / 800 : ℝ)) (273521 / 40000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (77 / 80 : ℝ) (1309117 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (77 / 80 : ℝ))) h 2
    have he :
        (Real.exp (77 / 80 : ℝ)) ^ 2 =
          Real.exp (2 * (77 / 80 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (273521 / 40000 : ℝ) - (77 / 80 : ℝ) / 2) / 32)
      (6021741 / 3125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_770 :
    ∀ u : ℝ, (77 / 80 : ℝ) ≤ u → u ≤ (771 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (7 / 2500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (77 / 80 : ℝ) (771 / 800 : ℝ) (3427571 / 500000 : ℝ) (6872309437081 / 1000000000000 : ℝ)
    (193015867 / 100000000 : ℝ) (1 / 1250000000 : ℝ) (7 / 2500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (77 / 80 : ℝ)) (3427571 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (771 / 800 : ℝ) (2621509 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (771 / 800 : ℝ))) h 2
    have he :
        (Real.exp (771 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (771 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3427571 / 500000 : ℝ) - (771 / 800 : ℝ) / 2) / 32)
      (193015867 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_771 :
    ∀ u : ℝ, (771 / 800 : ℝ) ≤ u → u ≤ (193 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (247 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (771 / 800 : ℝ) (193 / 200 : ℝ) (6872301 / 1000000 : ℝ) (430594502809 / 62500000000 : ℝ)
    (193337351 / 100000000 : ℝ) (7 / 10000000000 : ℝ) (247 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (771 / 800 : ℝ)) (6872301 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (193 / 200 : ℝ) (656197 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (193 / 200 : ℝ))) h 2
    have he :
        (Real.exp (193 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (193 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (6872301 / 1000000 : ℝ) - (193 / 200 : ℝ) / 2) / 32)
      (193337351 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_772 :
    ∀ u : ℝ, (193 / 200 : ℝ) ≤ u → u ≤ (773 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (31 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (193 / 200 : ℝ) (773 / 800 : ℝ) (6889503 / 1000000 : ℝ) (6906757181041 / 1000000000000 : ℝ)
    (193660187 / 100000000 : ℝ) (7 / 10000000000 : ℝ) (31 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (193 / 200 : ℝ)) (6889503 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (773 / 800 : ℝ) (2628071 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (773 / 800 : ℝ))) h 2
    have he :
        (Real.exp (773 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (773 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (6889503 / 1000000 : ℝ) - (773 / 800 : ℝ) / 2) / 32)
      (193660187 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_773 :
    ∀ u : ℝ, (773 / 800 : ℝ) ≤ u → u ≤ (387 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (249 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (773 / 800 : ℝ) (387 / 400 : ℝ) (1726687 / 250000 : ℝ) (1731011231041 / 250000000000 : ℝ)
    (193984381 / 100000000 : ℝ) (7 / 10000000000 : ℝ) (249 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (773 / 800 : ℝ)) (1726687 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (387 / 400 : ℝ) (1315679 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (387 / 400 : ℝ))) h 2
    have he :
        (Real.exp (387 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (387 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1726687 / 250000 : ℝ) - (387 / 400 : ℝ) / 2) / 32)
      (193984381 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_774 :
    ∀ u : ℝ, (387 / 400 : ℝ) ≤ u → u ≤ (31 / 32 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (43 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (387 / 400 : ℝ) (31 / 32 : ℝ) (6924037 / 1000000 : ℝ) (2776552249 / 400000000 : ℝ)
    (48577489 / 25000000 : ℝ) (3 / 5000000000 : ℝ) (43 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (387 / 400 : ℝ)) (6924037 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (31 / 32 : ℝ) (52693 / 20000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (31 / 32 : ℝ))) h 2
    have he :
        (Real.exp (31 / 32 : ℝ)) ^ 2 =
          Real.exp (2 * (31 / 32 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (6924037 / 1000000 : ℝ) - (31 / 32 : ℝ) / 2) / 32)
      (48577489 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_775 :
    ∀ u : ℝ, (31 / 32 : ℝ) ≤ u → u ≤ (97 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (27 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (31 / 32 : ℝ) (97 / 100 : ℝ) (867671 / 125000 : ℝ) (278350152921 / 40000000000 : ℝ)
    (2432961 / 1250000 : ℝ) (3 / 5000000000 : ℝ) (27 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (31 / 32 : ℝ)) (867671 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (97 / 100 : ℝ) (527589 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (97 / 100 : ℝ))) h 2
    have he :
        (Real.exp (97 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (97 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (867671 / 125000 : ℝ) - (97 / 100 : ℝ) / 2) / 32)
      (2432961 / 1250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_776 :
    ∀ u : ℝ, (97 / 100 : ℝ) ≤ u → u ≤ (777 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (217 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (97 / 100 : ℝ) (777 / 800 : ℝ) (869843 / 125000 : ℝ) (436010616721 / 62500000000 : ℝ)
    (38993043 / 20000000 : ℝ) (3 / 5000000000 : ℝ) (217 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (97 / 100 : ℝ)) (869843 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (777 / 800 : ℝ) (660311 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (777 / 800 : ℝ))) h 2
    have he :
        (Real.exp (777 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (777 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (869843 / 125000 : ℝ) - (777 / 800 : ℝ) / 2) / 32)
      (38993043 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_777 :
    ∀ u : ℝ, (777 / 800 : ℝ) ≤ u → u ≤ (389 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (91 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (777 / 800 : ℝ) (389 / 400 : ℝ) (3488081 / 500000 : ℝ) (437102132769 / 62500000000 : ℝ)
    (48823727 / 25000000 : ℝ) (1 / 2000000000 : ℝ) (91 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (777 / 800 : ℝ)) (3488081 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (389 / 400 : ℝ) (661137 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (389 / 400 : ℝ))) h 2
    have he :
        (Real.exp (389 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (389 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3488081 / 500000 : ℝ) - (389 / 400 : ℝ) / 2) / 32)
      (48823727 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_778 :
    ∀ u : ℝ, (389 / 400 : ℝ) ≤ u → u ≤ (779 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (183 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (389 / 400 : ℝ) (779 / 800 : ℝ) (874203 / 125000 : ℝ) (27387271081 / 3906250000 : ℝ)
    (48906501 / 25000000 : ℝ) (1 / 2000000000 : ℝ) (183 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (389 / 400 : ℝ)) (874203 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (779 / 800 : ℝ) (165491 / 62500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (779 / 800 : ℝ))) h 2
    have he :
        (Real.exp (779 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (779 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (874203 / 125000 : ℝ) - (779 / 800 : ℝ) / 2) / 32)
      (48906501 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_779 :
    ∀ u : ℝ, (779 / 800 : ℝ) ≤ u → u ≤ (39 / 40 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (23 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (779 / 800 : ℝ) (39 / 40 : ℝ) (701113 / 100000 : ℝ) (6863956801 / 976562500 : ℝ)
    (195958507 / 100000000 : ℝ) (1 / 2000000000 : ℝ) (23 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (779 / 800 : ℝ)) (701113 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (39 / 40 : ℝ) (82849 / 31250 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (39 / 40 : ℝ))) h 2
    have he :
        (Real.exp (39 / 40 : ℝ)) ^ 2 =
          Real.exp (2 * (39 / 40 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (701113 / 100000 : ℝ) - (39 / 40 : ℝ) / 2) / 32)
      (195958507 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_760
#print axioms hpThetaEnergyUpper_interval_779

end HodgeProofHP
