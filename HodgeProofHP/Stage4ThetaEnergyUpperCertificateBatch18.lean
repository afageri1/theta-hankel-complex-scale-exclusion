import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_360 :
    ∀ u : ℝ, (9 / 20 : ℝ) ≤ u → u ≤ (361 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1354867 / 6250000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (9 / 20 : ℝ) (361 / 800 : ℝ) (2459603 / 1000000 : ℝ) (616440108769 / 250000000000 : ℝ)
    (126402081 / 100000000 : ℝ) (1386133 / 2500000000 : ℝ) (1354867 / 6250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (9 / 20 : ℝ)) (2459603 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (361 / 800 : ℝ) (785137 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (361 / 800 : ℝ))) h 2
    have he :
        (Real.exp (361 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (361 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2459603 / 1000000 : ℝ) - (361 / 800 : ℝ) / 2) / 32)
      (126402081 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_361 :
    ∀ u : ℝ, (361 / 800 : ℝ) ≤ u → u ≤ (181 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (21395491 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (361 / 800 : ℝ) (181 / 400 : ℝ) (2465759 / 1000000 : ℝ) (617983082161 / 250000000000 : ℝ)
    (31618997 / 25000000 : ℝ) (2720893 / 5000000000 : ℝ) (21395491 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (361 / 800 : ℝ)) (2465759 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (181 / 400 : ℝ) (786119 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (181 / 400 : ℝ))) h 2
    have he :
        (Real.exp (181 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (181 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2465759 / 1000000 : ℝ) - (181 / 400 : ℝ) / 2) / 32)
      (31618997 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_362 :
    ∀ u : ℝ, (181 / 400 : ℝ) ≤ u → u ≤ (363 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (10557863 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (181 / 400 : ℝ) (363 / 800 : ℝ) (2471931 / 1000000 : ℝ) (99124855281 / 40000000000 : ℝ)
    (126550137 / 100000000 : ℝ) (1335169 / 2500000000 : ℝ) (10557863 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (181 / 400 : ℝ)) (2471931 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (363 / 800 : ℝ) (314841 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (363 / 800 : ℝ))) h 2
    have he :
        (Real.exp (363 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (363 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2471931 / 1000000 : ℝ) - (363 / 800 : ℝ) / 2) / 32)
      (126550137 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_363 :
    ∀ u : ℝ, (363 / 800 : ℝ) ≤ u → u ≤ (91 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (41677 / 200000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (363 / 800 : ℝ) (91 / 200 : ℝ) (2478119 / 1000000 : ℝ) (621081119569 / 250000000000 : ℝ)
    (7914033 / 6250000 : ℝ) (5241181 / 10000000000 : ℝ) (41677 / 200000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (363 / 800 : ℝ)) (2478119 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (91 / 200 : ℝ) (788087 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (91 / 200 : ℝ))) h 2
    have he :
        (Real.exp (91 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (91 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2478119 / 1000000 : ℝ) - (91 / 200 : ℝ) / 2) / 32)
      (7914033 / 6250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_364 :
    ∀ u : ℝ, (91 / 200 : ℝ) ≤ u → u ≤ (73 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (20563883 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (91 / 200 : ℝ) (73 / 160 : ℝ) (1242161 / 500000 : ℝ) (99621665641 / 40000000000 : ℝ)
    (126699149 / 100000000 : ℝ) (2571649 / 5000000000 : ℝ) (20563883 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (91 / 200 : ℝ)) (1242161 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (73 / 160 : ℝ) (315629 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (73 / 160 : ℝ))) h 2
    have he :
        (Real.exp (73 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (73 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1242161 / 500000 : ℝ) - (73 / 160 : ℝ) / 2) / 32)
      (126699149 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_365 :
    ∀ u : ℝ, (73 / 160 : ℝ) ≤ u → u ≤ (183 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (20291859 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (73 / 160 : ℝ) (183 / 400 : ℝ) (2490541 / 1000000 : ℝ) (2496776054161 / 1000000000000 : ℝ)
    (63387007 / 50000000 : ℝ) (5046989 / 10000000000 : ℝ) (20291859 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (73 / 160 : ℝ)) (2490541 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (183 / 400 : ℝ) (1580119 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (183 / 400 : ℝ))) h 2
    have he :
        (Real.exp (183 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (183 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2490541 / 1000000 : ℝ) - (183 / 400 : ℝ) / 2) / 32)
      (63387007 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_366 :
    ∀ u : ℝ, (183 / 400 : ℝ) ≤ u → u ≤ (367 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2502811 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (183 / 400 : ℝ) (367 / 800 : ℝ) (99871 / 40000 : ℝ) (9777452161 / 3906250000 : ℝ)
    (126849109 / 100000000 : ℝ) (19809 / 40000000 : ℝ) (2502811 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (183 / 400 : ℝ)) (99871 / 40000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (367 / 800 : ℝ) (98881 / 62500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (367 / 800 : ℝ))) h 2
    have he :
        (Real.exp (367 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (367 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (99871 / 40000 : ℝ) - (367 / 800 : ℝ) / 2) / 32)
      (126849109 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_367 :
    ∀ u : ℝ, (367 / 800 : ℝ) ≤ u → u ≤ (23 / 50 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (4938911 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (367 / 800 : ℝ) (23 / 50 : ℝ) (156439 / 62500 : ℝ) (627322609369 / 250000000000 : ℝ)
    (25384887 / 20000000 : ℝ) (2429531 / 5000000000 : ℝ) (4938911 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (367 / 800 : ℝ)) (156439 / 62500 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (23 / 50 : ℝ) (792037 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (23 / 50 : ℝ))) h 2
    have he :
        (Real.exp (23 / 50 : ℝ)) ^ 2 =
          Real.exp (2 * (23 / 50 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (156439 / 62500 : ℝ) - (23 / 50 : ℝ) / 2) / 32)
      (25384887 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_368 :
    ∀ u : ℝ, (23 / 50 : ℝ) ≤ u → u ≤ (369 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (9745683 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (23 / 50 : ℝ) (369 / 800 : ℝ) (250929 / 100000 : ℝ) (39305838049 / 15625000000 : ℝ)
    (63500009 / 50000000 : ℝ) (1191843 / 2500000000 : ℝ) (9745683 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (23 / 50 : ℝ)) (250929 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (369 / 800 : ℝ) (198257 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (369 / 800 : ℝ))) h 2
    have he :
        (Real.exp (369 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (369 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (250929 / 100000 : ℝ) - (369 / 800 : ℝ) / 2) / 32)
      (63500009 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_369 :
    ∀ u : ℝ, (369 / 800 : ℝ) ≤ u → u ≤ (37 / 80 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1201853 / 6250000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (369 / 800 : ℝ) (37 / 80 : ℝ) (2515571 / 1000000 : ℝ) (1576169401 / 625000000 : ℝ)
    (63537917 / 50000000 : ℝ) (467719 / 1000000000 : ℝ) (1201853 / 6250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (369 / 800 : ℝ)) (2515571 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (37 / 80 : ℝ) (39701 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (37 / 80 : ℝ))) h 2
    have he :
        (Real.exp (37 / 80 : ℝ)) ^ 2 =
          Real.exp (2 * (37 / 80 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2515571 / 1000000 : ℝ) - (37 / 80 : ℝ) / 2) / 32)
      (63537917 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_370 :
    ∀ u : ℝ, (37 / 80 : ℝ) ≤ u → u ≤ (371 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (474261 / 2500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (37 / 80 : ℝ) (371 / 800 : ℝ) (630467 / 250000 : ℝ) (632045670169 / 250000000000 : ℝ)
    (63575947 / 50000000 : ℝ) (2294243 / 5000000000 : ℝ) (474261 / 2500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (37 / 80 : ℝ)) (630467 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (371 / 800 : ℝ) (795013 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (371 / 800 : ℝ))) h 2
    have he :
        (Real.exp (371 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (371 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (630467 / 250000 : ℝ) - (371 / 800 : ℝ) / 2) / 32)
      (63575947 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_371 :
    ∀ u : ℝ, (371 / 800 : ℝ) ≤ u → u ≤ (93 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (18713837 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (371 / 800 : ℝ) (93 / 200 : ℝ) (126409 / 50000 : ℝ) (101380470409 / 40000000000 : ℝ)
    (127228187 / 100000000 : ℝ) (4501251 / 10000000000 : ℝ) (18713837 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (371 / 800 : ℝ)) (126409 / 50000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (93 / 200 : ℝ) (318403 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (93 / 200 : ℝ))) h 2
    have he :
        (Real.exp (93 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (93 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (126409 / 50000 : ℝ) - (93 / 200 : ℝ) / 2) / 32)
      (127228187 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_372 :
    ∀ u : ℝ, (93 / 200 : ℝ) ≤ u → u ≤ (373 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (9229829 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (93 / 200 : ℝ) (373 / 800 : ℝ) (2534509 / 1000000 : ℝ) (635213782009 / 250000000000 : ℝ)
    (63652369 / 50000000 : ℝ) (4415439 / 10000000000 : ℝ) (9229829 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (93 / 200 : ℝ)) (2534509 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (373 / 800 : ℝ) (797003 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (373 / 800 : ℝ))) h 2
    have he :
        (Real.exp (373 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (373 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2534509 / 1000000 : ℝ) - (373 / 800 : ℝ) / 2) / 32)
      (63652369 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_373 :
    ∀ u : ℝ, (373 / 800 : ℝ) ≤ u → u ≤ (187 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (4552019 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (373 / 800 : ℝ) (187 / 400 : ℝ) (2540853 / 1000000 : ℝ) (159201 / 62500 : ℝ)
    (63690761 / 50000000 : ℝ) (216553 / 500000000 : ℝ) (4552019 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (373 / 800 : ℝ)) (2540853 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (187 / 400 : ℝ) (399 / 250 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (187 / 400 : ℝ))) h 2
    have he :
        (Real.exp (187 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (187 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2540853 / 1000000 : ℝ) - (187 / 400 : ℝ) / 2) / 32)
      (63690761 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_374 :
    ∀ u : ℝ, (187 / 400 : ℝ) ≤ u → u ≤ (15 / 32 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (17958957 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (187 / 400 : ℝ) (15 / 32 : ℝ) (2547213 / 1000000 : ℝ) (159599451001 / 62500000000 : ℝ)
    (127458553 / 100000000 : ℝ) (4248079 / 10000000000 : ℝ) (17958957 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (187 / 400 : ℝ)) (2547213 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (15 / 32 : ℝ) (399499 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (15 / 32 : ℝ))) h 2
    have he :
        (Real.exp (15 / 32 : ℝ)) ^ 2 =
          Real.exp (2 * (15 / 32 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2547213 / 1000000 : ℝ) - (15 / 32 : ℝ) / 2) / 32)
      (127458553 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_375 :
    ∀ u : ℝ, (15 / 32 : ℝ) ≤ u → u ≤ (47 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (354247 / 2000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (15 / 32 : ℝ) (47 / 100 : ℝ) (2553589 / 1000000 : ℝ) (102399360001 / 40000000000 : ℝ)
    (127535831 / 100000000 : ℝ) (2083239 / 5000000000 : ℝ) (354247 / 2000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (15 / 32 : ℝ)) (2553589 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (47 / 100 : ℝ) (319999 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (47 / 100 : ℝ))) h 2
    have he :
        (Real.exp (47 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (47 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2553589 / 1000000 : ℝ) - (47 / 100 : ℝ) / 2) / 32)
      (127535831 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_376 :
    ∀ u : ℝ, (47 / 100 : ℝ) ≤ u → u ≤ (377 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (17468199 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (47 / 100 : ℝ) (377 / 800 : ℝ) (2559981 / 1000000 : ℝ) (160399449001 / 62500000000 : ℝ)
    (31903339 / 25000000 : ℝ) (25539 / 62500000 : ℝ) (17468199 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (47 / 100 : ℝ)) (2559981 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (377 / 800 : ℝ) (400499 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (377 / 800 : ℝ))) h 2
    have he :
        (Real.exp (377 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (377 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2559981 / 1000000 : ℝ) - (377 / 800 : ℝ) / 2) / 32)
      (31903339 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_377 :
    ∀ u : ℝ, (377 / 800 : ℝ) ≤ u → u ≤ (189 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1076659 / 6250000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (377 / 800 : ℝ) (189 / 400 : ℝ) (2566389 / 1000000 : ℝ) (160801 / 62500 : ℝ)
    (127691129 / 100000000 : ℝ) (2003673 / 5000000000 : ℝ) (1076659 / 6250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (377 / 800 : ℝ)) (2566389 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (189 / 400 : ℝ) (401 / 250 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (189 / 400 : ℝ))) h 2
    have he :
        (Real.exp (189 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (189 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2566389 / 1000000 : ℝ) - (189 / 400 : ℝ) / 2) / 32)
      (127691129 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_378 :
    ∀ u : ℝ, (189 / 400 : ℝ) ≤ u → u ≤ (379 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (679493 / 4000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (189 / 400 : ℝ) (379 / 800 : ℝ) (2572813 / 1000000 : ℝ) (644813818009 / 250000000000 : ℝ)
    (127769149 / 100000000 : ℝ) (1964889 / 5000000000 : ℝ) (679493 / 4000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (189 / 400 : ℝ)) (2572813 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (379 / 800 : ℝ) (803003 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (379 / 800 : ℝ))) h 2
    have he :
        (Real.exp (379 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (379 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2572813 / 1000000 : ℝ) - (379 / 800 : ℝ) / 2) / 32)
      (127769149 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_379 :
    ∀ u : ℝ, (379 / 800 : ℝ) ≤ u → u ≤ (19 / 40 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (8375289 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (379 / 800 : ℝ) (19 / 40 : ℝ) (2579253 / 1000000 : ℝ) (103428489609 / 40000000000 : ℝ)
    (63923709 / 50000000 : ℝ) (3853517 / 10000000000 : ℝ) (8375289 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (379 / 800 : ℝ)) (2579253 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (19 / 40 : ℝ) (321603 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (19 / 40 : ℝ))) h 2
    have he :
        (Real.exp (19 / 40 : ℝ)) ^ 2 =
          Real.exp (2 * (19 / 40 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2579253 / 1000000 : ℝ) - (19 / 40 : ℝ) / 2) / 32)
      (63923709 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_360
#print axioms hpThetaEnergyUpper_interval_379

end HodgeProofHP
