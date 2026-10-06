import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_740 :
    ∀ u : ℝ, (37 / 40 : ℝ) ≤ u → u ≤ (741 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1019 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (37 / 40 : ℝ) (741 / 800 : ℝ) (1271963 / 200000 : ℝ) (6375741150529 / 1000000000000 : ℝ)
    (45991657 / 25000000 : ℝ) (17 / 5000000000 : ℝ) (1019 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (37 / 40 : ℝ)) (1271963 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (741 / 800 : ℝ) (2525023 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (741 / 800 : ℝ))) h 2
    have he :
        (Real.exp (741 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (741 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1271963 / 200000 : ℝ) - (741 / 800 : ℝ) / 2) / 32)
      (45991657 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_741 :
    ∀ u : ℝ, (741 / 800 : ℝ) ≤ u → u ≤ (371 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (497 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (741 / 800 : ℝ) (371 / 400 : ℝ) (3187867 / 500000 : ℝ) (6391699168761 / 1000000000000 : ℝ)
    (9212531 / 5000000 : ℝ) (33 / 10000000000 : ℝ) (497 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (741 / 800 : ℝ)) (3187867 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (371 / 400 : ℝ) (2528181 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (371 / 400 : ℝ))) h 2
    have he :
        (Real.exp (371 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (371 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3187867 / 500000 : ℝ) - (371 / 400 : ℝ) / 2) / 32)
      (9212531 / 5000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_742 :
    ∀ u : ℝ, (371 / 400 : ℝ) ≤ u → u ≤ (743 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (939 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (371 / 400 : ℝ) (743 / 800 : ℝ) (3195847 / 500000 : ℝ) (25030087681 / 3906250000 : ℝ)
    (11533487 / 6250000 : ℝ) (31 / 10000000000 : ℝ) (939 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (371 / 400 : ℝ)) (3195847 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (743 / 800 : ℝ) (158209 / 62500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (743 / 800 : ℝ))) h 2
    have he :
        (Real.exp (743 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (743 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3195847 / 500000 : ℝ) - (743 / 800 : ℝ) / 2) / 32)
      (11533487 / 6250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_743 :
    ∀ u : ℝ, (743 / 800 : ℝ) ≤ u → u ≤ (93 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (913 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (743 / 800 : ℝ) (93 / 100 : ℝ) (6407693 / 1000000 : ℝ) (64237409401 / 10000000000 : ℝ)
    (184822113 / 100000000 : ℝ) (3 / 1000000000 : ℝ) (913 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (743 / 800 : ℝ)) (6407693 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (93 / 100 : ℝ) (253451 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (93 / 100 : ℝ))) h 2
    have he :
        (Real.exp (93 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (93 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (6407693 / 1000000 : ℝ) - (93 / 100 : ℝ) / 2) / 32)
      (184822113 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_744 :
    ∀ u : ℝ, (93 / 100 : ℝ) ≤ u → u ≤ (149 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (857 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (93 / 100 : ℝ) (149 / 160 : ℝ) (1605933 / 250000 : ℝ) (1006221841 / 156250000 : ℝ)
    (46277401 / 25000000 : ℝ) (7 / 2500000000 : ℝ) (857 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (93 / 100 : ℝ)) (1605933 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (149 / 160 : ℝ) (31721 / 12500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (149 / 160 : ℝ))) h 2
    have he :
        (Real.exp (149 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (149 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1605933 / 250000 : ℝ) - (149 / 160 : ℝ) / 2) / 32)
      (46277401 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_745 :
    ∀ u : ℝ, (149 / 160 : ℝ) ≤ u → u ≤ (373 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (83 / 10000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (149 / 160 : ℝ) (373 / 400 : ℝ) (6439811 / 1000000 : ℝ) (1613984762329 / 250000000000 : ℝ)
    (185398271 / 100000000 : ℝ) (27 / 10000000000 : ℝ) (83 / 10000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (149 / 160 : ℝ)) (6439811 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (373 / 400 : ℝ) (1270427 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (373 / 400 : ℝ))) h 2
    have he :
        (Real.exp (373 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (373 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (6439811 / 1000000 : ℝ) - (373 / 400 : ℝ) / 2) / 32)
      (185398271 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_746 :
    ∀ u : ℝ, (373 / 400 : ℝ) ≤ u → u ≤ (747 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (201 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (373 / 400 : ℝ) (747 / 800 : ℝ) (6455931 / 1000000 : ℝ) (6320409001 / 976562500 : ℝ)
    (92844067 / 50000000 : ℝ) (13 / 5000000000 : ℝ) (201 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (373 / 400 : ℝ)) (6455931 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (747 / 800 : ℝ) (79501 / 31250 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (747 / 800 : ℝ))) h 2
    have he :
        (Real.exp (747 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (747 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (6455931 / 1000000 : ℝ) - (747 / 800 : ℝ) / 2) / 32)
      (92844067 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_747 :
    ∀ u : ℝ, (747 / 800 : ℝ) ≤ u → u ≤ (187 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (373 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (747 / 800 : ℝ) (187 / 200 : ℝ) (6472091 / 1000000 : ℝ) (1622074790449 / 250000000000 : ℝ)
    (185979181 / 100000000 : ℝ) (3 / 1250000000 : ℝ) (373 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (747 / 800 : ℝ)) (6472091 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (187 / 200 : ℝ) (1273607 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (187 / 200 : ℝ))) h 2
    have he :
        (Real.exp (187 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (187 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (6472091 / 1000000 : ℝ) - (187 / 200 : ℝ) / 2) / 32)
      (185979181 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_748 :
    ∀ u : ℝ, (187 / 200 : ℝ) ≤ u → u ≤ (749 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (719 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (187 / 200 : ℝ) (749 / 800 : ℝ) (6488291 / 1000000 : ℝ) (2540836 / 390625 : ℝ)
    (37254283 / 20000000 : ℝ) (23 / 10000000000 : ℝ) (719 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (187 / 200 : ℝ)) (6488291 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (749 / 800 : ℝ) (1594 / 625 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (749 / 800 : ℝ))) h 2
    have he :
        (Real.exp (749 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (749 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (6488291 / 1000000 : ℝ) - (749 / 800 : ℝ) / 2) / 32)
      (37254283 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_749 :
    ∀ u : ℝ, (749 / 800 : ℝ) ≤ u → u ≤ (15 / 16 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (691 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (749 / 800 : ℝ) (15 / 16 : ℝ) (1626133 / 250000 : ℝ) (65208218881 / 10000000000 : ℝ)
    (186564859 / 100000000 : ℝ) (11 / 5000000000 : ℝ) (691 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (749 / 800 : ℝ)) (1626133 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (15 / 16 : ℝ) (255359 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (15 / 16 : ℝ))) h 2
    have he :
        (Real.exp (15 / 16 : ℝ)) ^ 2 =
          Real.exp (2 * (15 / 16 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1626133 / 250000 : ℝ) - (15 / 16 : ℝ) / 2) / 32)
      (186564859 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_750 :
    ∀ u : ℝ, (15 / 16 : ℝ) ≤ u → u ≤ (751 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (663 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (15 / 16 : ℝ) (751 / 800 : ℝ) (3260407 / 500000 : ℝ) (25535720401 / 3906250000 : ℝ)
    (186859517 / 100000000 : ℝ) (21 / 10000000000 : ℝ) (663 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (15 / 16 : ℝ)) (3260407 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (751 / 800 : ℝ) (159799 / 62500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (751 / 800 : ℝ))) h 2
    have he :
        (Real.exp (751 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (751 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3260407 / 500000 : ℝ) - (751 / 800 : ℝ) / 2) / 32)
      (186859517 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_751 :
    ∀ u : ℝ, (751 / 800 : ℝ) ≤ u → u ≤ (47 / 50 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (127 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (751 / 800 : ℝ) (47 / 50 : ℝ) (408571 / 62500 : ℝ) (1638376960081 / 250000000000 : ℝ)
    (1497243 / 800000 : ℝ) (1 / 500000000 : ℝ) (127 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (751 / 800 : ℝ)) (408571 / 62500 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (47 / 50 : ℝ) (1279991 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (47 / 50 : ℝ))) h 2
    have he :
        (Real.exp (47 / 50 : ℝ)) ^ 2 =
          Real.exp (2 * (47 / 50 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (408571 / 62500 : ℝ) - (47 / 50 : ℝ) / 2) / 32)
      (1497243 / 800000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_752 :
    ∀ u : ℝ, (47 / 50 : ℝ) ≤ u → u ≤ (753 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (303 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (47 / 50 : ℝ) (753 / 800 : ℝ) (13107 / 2000 : ℝ) (25663719601 / 3906250000 : ℝ)
    (93726237 / 50000000 : ℝ) (19 / 10000000000 : ℝ) (303 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (47 / 50 : ℝ)) (13107 / 2000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (753 / 800 : ℝ) (160199 / 62500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (753 / 800 : ℝ))) h 2
    have he :
        (Real.exp (753 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (753 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (13107 / 2000 : ℝ) - (753 / 800 : ℝ) / 2) / 32)
      (93726237 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_753 :
    ∀ u : ℝ, (753 / 800 : ℝ) ≤ u → u ≤ (377 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (577 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (753 / 800 : ℝ) (377 / 400 : ℝ) (410619 / 62500 : ℝ) (65863576321 / 10000000000 : ℝ)
    (187750781 / 100000000 : ℝ) (9 / 5000000000 : ℝ) (577 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (753 / 800 : ℝ)) (410619 / 62500 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (377 / 400 : ℝ) (256639 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (377 / 400 : ℝ))) h 2
    have he :
        (Real.exp (377 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (377 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (410619 / 62500 : ℝ) - (377 / 400 : ℝ) / 2) / 32)
      (187750781 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_754 :
    ∀ u : ℝ, (377 / 400 : ℝ) ≤ u → u ≤ (151 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (137 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (377 / 400 : ℝ) (151 / 160 : ℝ) (6586349 / 1000000 : ℝ) (2579236 / 390625 : ℝ)
    (2350629 / 1250000 : ℝ) (17 / 10000000000 : ℝ) (137 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (377 / 400 : ℝ)) (6586349 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (151 / 160 : ℝ) (1606 / 625 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (151 / 160 : ℝ))) h 2
    have he :
        (Real.exp (151 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (151 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (6586349 / 1000000 : ℝ) - (151 / 160 : ℝ) / 2) / 32)
      (2350629 / 1250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_755 :
    ∀ u : ℝ, (151 / 160 : ℝ) ≤ u → u ≤ (189 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (519 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (151 / 160 : ℝ) (189 / 200 : ℝ) (1320567 / 200000 : ℝ) (1654842969649 / 250000000000 : ℝ)
    (94175547 / 50000000 : ℝ) (1 / 625000000 : ℝ) (519 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (151 / 160 : ℝ)) (1320567 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (189 / 200 : ℝ) (1286407 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (189 / 200 : ℝ))) h 2
    have he :
        (Real.exp (189 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (189 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1320567 / 200000 : ℝ) - (189 / 200 : ℝ) / 2) / 32)
      (94175547 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_756 :
    ∀ u : ℝ, (189 / 200 : ℝ) ≤ u → u ≤ (757 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (521 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (189 / 200 : ℝ) (757 / 800 : ℝ) (6619363 / 1000000 : ℝ) (6480411001 / 976562500 : ℝ)
    (188653127 / 100000000 : ℝ) (1 / 625000000 : ℝ) (521 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (189 / 200 : ℝ)) (6619363 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (757 / 800 : ℝ) (80501 / 31250 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (757 / 800 : ℝ))) h 2
    have he :
        (Real.exp (757 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (757 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (6619363 / 1000000 : ℝ) - (757 / 800 : ℝ) / 2) / 32)
      (188653127 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_757 :
    ∀ u : ℝ, (757 / 800 : ℝ) ≤ u → u ≤ (379 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (491 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (757 / 800 : ℝ) (379 / 400 : ℝ) (1658983 / 250000 : ℝ) (1663137799129 / 250000000000 : ℝ)
    (47239101 / 25000000 : ℝ) (3 / 2000000000 : ℝ) (491 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (757 / 800 : ℝ)) (1658983 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (379 / 400 : ℝ) (1289627 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (379 / 400 : ℝ))) h 2
    have he :
        (Real.exp (379 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (379 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1658983 / 250000 : ℝ) - (379 / 400 : ℝ) / 2) / 32)
      (47239101 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_758 :
    ∀ u : ℝ, (379 / 400 : ℝ) ≤ u → u ≤ (759 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (461 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (379 / 400 : ℝ) (759 / 800 : ℝ) (6652543 / 1000000 : ℝ) (1042062961 / 156250000 : ℝ)
    (189260949 / 100000000 : ℝ) (7 / 5000000000 : ℝ) (461 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (379 / 400 : ℝ)) (6652543 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (759 / 800 : ℝ) (32281 / 12500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (759 / 800 : ℝ))) h 2
    have he :
        (Real.exp (759 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (759 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (6652543 / 1000000 : ℝ) - (759 / 800 : ℝ) / 2) / 32)
      (189260949 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_759 :
    ∀ u : ℝ, (759 / 800 : ℝ) ≤ u → u ≤ (19 / 20 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (43 / 10000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (759 / 800 : ℝ) (19 / 20 : ℝ) (1333839 / 200000 : ℝ) (66858962041 / 10000000000 : ℝ)
    (47391687 / 25000000 : ℝ) (13 / 10000000000 : ℝ) (43 / 10000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (759 / 800 : ℝ)) (1333839 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (19 / 20 : ℝ) (258571 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (19 / 20 : ℝ))) h 2
    have he :
        (Real.exp (19 / 20 : ℝ)) ^ 2 =
          Real.exp (2 * (19 / 20 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1333839 / 200000 : ℝ) - (19 / 20 : ℝ) / 2) / 32)
      (47391687 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_740
#print axioms hpThetaEnergyUpper_interval_759

end HodgeProofHP
