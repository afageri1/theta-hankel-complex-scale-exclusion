import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_520 :
    ∀ u : ℝ, (13 / 20 : ℝ) ≤ u → u ≤ (521 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (64413 / 5000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (13 / 20 : ℝ) (521 / 800 : ℝ) (229331 / 62500 : ℝ) (3678482335969 / 1000000000000 : ℝ)
    (141888859 / 100000000 : ℝ) (27459 / 2000000000 : ℝ) (64413 / 5000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (13 / 20 : ℝ)) (229331 / 62500 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (521 / 800 : ℝ) (1917937 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (521 / 800 : ℝ))) h 2
    have he :
        (Real.exp (521 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (521 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (229331 / 62500 : ℝ) - (521 / 800 : ℝ) / 2) / 32)
      (141888859 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_521 :
    ∀ u : ℝ, (521 / 800 : ℝ) ≤ u → u ≤ (261 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (39349 / 3125000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (521 / 800 : ℝ) (261 / 400 : ℝ) (3678481 / 1000000 : ℝ) (14405040441 / 3906250000 : ℝ)
    (5680561 / 4000000 : ℝ) (33369 / 2500000000 : ℝ) (39349 / 3125000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (521 / 800 : ℝ)) (3678481 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (261 / 400 : ℝ) (120021 / 62500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (261 / 400 : ℝ))) h 2
    have he :
        (Real.exp (261 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (261 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3678481 / 1000000 : ℝ) - (261 / 400 : ℝ) / 2) / 32)
      (5680561 / 4000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_522 :
    ∀ u : ℝ, (261 / 400 : ℝ) ≤ u → u ≤ (523 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (246127 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (261 / 400 : ℝ) (523 / 800 : ℝ) (3687689 / 1000000 : ℝ) (924230354161 / 250000000000 : ℝ)
    (142139621 / 100000000 : ℝ) (129753 / 10000000000 : ℝ) (246127 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (261 / 400 : ℝ)) (3687689 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (523 / 800 : ℝ) (961369 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (523 / 800 : ℝ))) h 2
    have he :
        (Real.exp (523 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (523 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3687689 / 1000000 : ℝ) - (523 / 800 : ℝ) / 2) / 32)
      (142139621 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_523 :
    ∀ u : ℝ, (523 / 800 : ℝ) ≤ u → u ≤ (131 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (601331 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (523 / 800 : ℝ) (131 / 200 : ℝ) (3696919 / 1000000 : ℝ) (3706175570449 / 1000000000000 : ℝ)
    (35566409 / 25000000 : ℝ) (1009 / 80000000 : ℝ) (601331 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (523 / 800 : ℝ)) (3696919 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (131 / 200 : ℝ) (1925143 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (131 / 200 : ℝ))) h 2
    have he :
        (Real.exp (131 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (131 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3696919 / 1000000 : ℝ) - (131 / 200 : ℝ) / 2) / 32)
      (35566409 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_524 :
    ∀ u : ℝ, (131 / 200 : ℝ) ≤ u → u ≤ (21 / 32 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (293811 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (131 / 200 : ℝ) (21 / 32 : ℝ) (3706173 / 1000000 : ℝ) (3715452857601 / 1000000000000 : ℝ)
    (142392097 / 100000000 : ℝ) (12259 / 1000000000 : ℝ) (293811 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (131 / 200 : ℝ)) (3706173 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (21 / 32 : ℝ) (1927551 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (21 / 32 : ℝ))) h 2
    have he :
        (Real.exp (21 / 32 : ℝ)) ^ 2 =
          Real.exp (2 * (21 / 32 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3706173 / 1000000 : ℝ) - (21 / 32 : ℝ) / 2) / 32)
      (142392097 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_525 :
    ∀ u : ℝ, (21 / 32 : ℝ) ≤ u → u ≤ (263 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (17943 / 1562500 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (21 / 32 : ℝ) (263 / 400 : ℝ) (74309 / 20000 : ℝ) (931188330361 / 250000000000 : ℝ)
    (142518993 / 100000000 : ℝ) (14893 / 1250000000 : ℝ) (17943 / 1562500 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (21 / 32 : ℝ)) (74309 / 20000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (263 / 400 : ℝ) (964981 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (263 / 400 : ℝ))) h 2
    have he :
        (Real.exp (263 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (263 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (74309 / 20000 : ℝ) - (263 / 400 : ℝ) / 2) / 32)
      (142518993 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_526 :
    ∀ u : ℝ, (263 / 400 : ℝ) ≤ u → u ≤ (527 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1122007 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (263 / 400 : ℝ) (527 / 800 : ℝ) (14899 / 4000 : ℝ) (58344953209 / 15625000000 : ℝ)
    (35661581 / 25000000 : ℝ) (28947 / 2500000000 : ℝ) (1122007 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (263 / 400 : ℝ)) (14899 / 4000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (527 / 800 : ℝ) (241547 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (527 / 800 : ℝ))) h 2
    have he :
        (Real.exp (527 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (527 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (14899 / 4000 : ℝ) - (527 / 800 : ℝ) / 2) / 32)
      (35661581 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_527 :
    ∀ u : ℝ, (527 / 800 : ℝ) ≤ u → u ≤ (33 / 50 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1096173 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (527 / 800 : ℝ) (33 / 50 : ℝ) (1867037 / 500000 : ℝ) (3743423952849 / 1000000000000 : ℝ)
    (28554821 / 20000000 : ℝ) (112517 / 10000000000 : ℝ) (1096173 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (527 / 800 : ℝ)) (1867037 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (33 / 50 : ℝ) (1934793 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (33 / 50 : ℝ))) h 2
    have he :
        (Real.exp (33 / 50 : ℝ)) ^ 2 =
          Real.exp (2 * (33 / 50 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1867037 / 500000 : ℝ) - (33 / 50 : ℝ) / 2) / 32)
      (28554821 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_528 :
    ∀ u : ℝ, (33 / 50 : ℝ) ≤ u → u ≤ (529 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (53543 / 5000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (33 / 50 : ℝ) (529 / 800 : ℝ) (3743421 / 1000000 : ℝ) (3752794207369 / 1000000000000 : ℝ)
    (71451161 / 50000000 : ℝ) (109331 / 10000000000 : ℝ) (53543 / 5000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (33 / 50 : ℝ)) (3743421 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (529 / 800 : ℝ) (1937213 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (529 / 800 : ℝ))) h 2
    have he :
        (Real.exp (529 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (529 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3743421 / 1000000 : ℝ) - (529 / 800 : ℝ) / 2) / 32)
      (71451161 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_529 :
    ∀ u : ℝ, (529 / 800 : ℝ) ≤ u → u ≤ (53 / 80 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (52303 / 5000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (529 / 800 : ℝ) (53 / 80 : ℝ) (3752791 / 1000000 : ℝ) (235136738281 / 62500000000 : ℝ)
    (71515489 / 50000000 : ℝ) (26557 / 2500000000 : ℝ) (52303 / 5000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (529 / 800 : ℝ)) (3752791 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (53 / 80 : ℝ) (484909 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (53 / 80 : ℝ))) h 2
    have he :
        (Real.exp (53 / 80 : ℝ)) ^ 2 =
          Real.exp (2 * (53 / 80 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3752791 / 1000000 : ℝ) - (53 / 80 : ℝ) / 2) / 32)
      (71515489 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_530 :
    ∀ u : ℝ, (53 / 80 : ℝ) ≤ u → u ≤ (531 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1021753 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (53 / 80 : ℝ) (531 / 800 : ℝ) (752437 / 200000 : ℝ) (942901202961 / 250000000000 : ℝ)
    (143160087 / 100000000 : ℝ) (20641 / 2000000000 : ℝ) (1021753 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (53 / 80 : ℝ)) (752437 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (531 / 800 : ℝ) (971031 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (531 / 800 : ℝ))) h 2
    have he :
        (Real.exp (531 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (531 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (752437 / 200000 : ℝ) - (531 / 800 : ℝ) / 2) / 32)
      (143160087 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_531 :
    ∀ u : ℝ, (531 / 800 : ℝ) ≤ u → u ≤ (133 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (997929 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (531 / 800 : ℝ) (133 / 200 : ℝ) (1885801 / 500000 : ℝ) (3781045249081 / 1000000000000 : ℝ)
    (28657927 / 20000000 : ℝ) (5013 / 500000000 : ℝ) (997929 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (531 / 800 : ℝ)) (1885801 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (133 / 200 : ℝ) (1944491 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (133 / 200 : ℝ))) h 2
    have he :
        (Real.exp (133 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (133 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1885801 / 500000 : ℝ) - (133 / 200 : ℝ) / 2) / 32)
      (28657927 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_532 :
    ∀ u : ℝ, (133 / 200 : ℝ) ≤ u → u ≤ (533 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (4873 / 500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (133 / 200 : ℝ) (533 / 800 : ℝ) (3781043 / 1000000 : ℝ) (3790509167929 / 1000000000000 : ℝ)
    (143419639 / 100000000 : ℝ) (97393 / 10000000000 : ℝ) (4873 / 500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (133 / 200 : ℝ)) (3781043 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (533 / 800 : ℝ) (1946923 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (533 / 800 : ℝ))) h 2
    have he :
        (Real.exp (533 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (533 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3781043 / 1000000 : ℝ) - (533 / 800 : ℝ) / 2) / 32)
      (143419639 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_533 :
    ∀ u : ℝ, (533 / 800 : ℝ) ≤ u → u ≤ (267 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (190347 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (533 / 800 : ℝ) (267 / 400 : ℝ) (3790507 / 1000000 : ℝ) (949999153041 / 250000000000 : ℝ)
    (35887521 / 25000000 : ℝ) (473 / 50000000 : ℝ) (190347 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (533 / 800 : ℝ)) (3790507 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (267 / 400 : ℝ) (974679 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (267 / 400 : ℝ))) h 2
    have he :
        (Real.exp (267 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (267 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3790507 / 1000000 : ℝ) - (267 / 400 : ℝ) / 2) / 32)
      (35887521 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_534 :
    ∀ u : ℝ, (267 / 400 : ℝ) ≤ u → u ≤ (107 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (185869 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (267 / 400 : ℝ) (107 / 160 : ℝ) (759999 / 200000 : ℝ) (3809511529209 / 1000000000000 : ℝ)
    (143680987 / 100000000 : ℝ) (91881 / 10000000000 : ℝ) (185869 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (267 / 400 : ℝ)) (759999 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (107 / 160 : ℝ) (1951797 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (107 / 160 : ℝ))) h 2
    have he :
        (Real.exp (107 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (107 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (759999 / 200000 : ℝ) - (107 / 160 : ℝ) / 2) / 32)
      (143680987 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_535 :
    ∀ u : ℝ, (107 / 160 : ℝ) ≤ u → u ≤ (67 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (453703 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (107 / 160 : ℝ) (67 / 100 : ℝ) (3809507 / 1000000 : ℝ) (954761540161 / 250000000000 : ℝ)
    (143812347 / 100000000 : ℝ) (89233 / 10000000000 : ℝ) (453703 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (107 / 160 : ℝ)) (3809507 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (67 / 100 : ℝ) (977119 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (67 / 100 : ℝ))) h 2
    have he :
        (Real.exp (67 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (67 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3809507 / 1000000 : ℝ) - (67 / 100 : ℝ) / 2) / 32)
      (143812347 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_536 :
    ∀ u : ℝ, (67 / 100 : ℝ) ≤ u → u ≤ (537 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (5537 / 625000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (67 / 100 : ℝ) (537 / 800 : ℝ) (3819043 / 1000000 : ℝ) (957151112281 / 250000000000 : ℝ)
    (143944167 / 100000000 : ℝ) (17331 / 2000000000 : ℝ) (5537 / 625000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (67 / 100 : ℝ)) (3819043 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (537 / 800 : ℝ) (978341 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (537 / 800 : ℝ))) h 2
    have he :
        (Real.exp (537 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (537 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3819043 / 1000000 : ℝ) - (537 / 800 : ℝ) / 2) / 32)
      (143944167 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_537 :
    ∀ u : ℝ, (537 / 800 : ℝ) ≤ u → u ≤ (269 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (864877 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (537 / 800 : ℝ) (269 / 400 : ℝ) (1914301 / 500000 : ℝ) (38381903569 / 10000000000 : ℝ)
    (144076433 / 100000000 : ℝ) (16829 / 2000000000 : ℝ) (864877 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (537 / 800 : ℝ)) (1914301 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (269 / 400 : ℝ) (195913 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (269 / 400 : ℝ))) h 2
    have he :
        (Real.exp (269 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (269 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1914301 / 500000 : ℝ) - (269 / 400 : ℝ) / 2) / 32)
      (144076433 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_538 :
    ∀ u : ℝ, (269 / 400 : ℝ) ≤ u → u ≤ (539 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (52767 / 6250000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (269 / 400 : ℝ) (539 / 800 : ℝ) (1919093 / 500000 : ℝ) (9619490241 / 2500000000 : ℝ)
    (72104587 / 50000000 : ℝ) (40851 / 5000000000 : ℝ) (52767 / 6250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (269 / 400 : ℝ)) (1919093 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (539 / 800 : ℝ) (98079 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (539 / 800 : ℝ))) h 2
    have he :
        (Real.exp (539 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (539 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1919093 / 500000 : ℝ) - (539 / 800 : ℝ) / 2) / 32)
      (72104587 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_539 :
    ∀ u : ℝ, (539 / 800 : ℝ) ≤ u → u ≤ (27 / 40 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (164817 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (539 / 800 : ℝ) (27 / 40 : ℝ) (3847793 / 1000000 : ℝ) (3857425625089 / 1000000000000 : ℝ)
    (144342363 / 100000000 : ℝ) (79323 / 10000000000 : ℝ) (164817 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (539 / 800 : ℝ)) (3847793 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (27 / 40 : ℝ) (1964033 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (27 / 40 : ℝ))) h 2
    have he :
        (Real.exp (27 / 40 : ℝ)) ^ 2 =
          Real.exp (2 * (27 / 40 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3847793 / 1000000 : ℝ) - (27 / 40 : ℝ) / 2) / 32)
      (144342363 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_520
#print axioms hpThetaEnergyUpper_interval_539

end HodgeProofHP
