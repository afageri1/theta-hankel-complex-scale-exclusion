import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_540 :
    ∀ u : ℝ, (27 / 40 : ℝ) ≤ u → u ≤ (541 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (402163 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (27 / 40 : ℝ) (541 / 800 : ℝ) (154297 / 40000 : ℝ) (38670829201 / 10000000000 : ℝ)
    (144476029 / 100000000 : ℝ) (4813 / 625000000 : ℝ) (402163 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (27 / 40 : ℝ)) (154297 / 40000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (541 / 800 : ℝ) (196649 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (541 / 800 : ℝ))) h 2
    have he :
        (Real.exp (541 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (541 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (154297 / 40000 : ℝ) - (541 / 800 : ℝ) / 2) / 32)
      (144476029 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_541 :
    ∀ u : ℝ, (541 / 800 : ℝ) ≤ u → u ≤ (271 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (392491 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (541 / 800 : ℝ) (271 / 400 : ℝ) (3867081 / 1000000 : ℝ) (1550705641 / 400000000 : ℝ)
    (1807627 / 1250000 : ℝ) (14951 / 2000000000 : ℝ) (392491 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (541 / 800 : ℝ)) (3867081 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (271 / 400 : ℝ) (39379 / 20000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (271 / 400 : ℝ))) h 2
    have he :
        (Real.exp (271 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (271 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3867081 / 1000000 : ℝ) - (271 / 400 : ℝ) / 2) / 32)
      (1807627 / 1250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_542 :
    ∀ u : ℝ, (271 / 400 : ℝ) ≤ u → u ≤ (543 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (766049 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (271 / 400 : ℝ) (543 / 800 : ℝ) (96919 / 25000 : ℝ) (242904079609 / 62500000000 : ℝ)
    (72372371 / 50000000 : ℝ) (72563 / 10000000000 : ℝ) (766049 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (271 / 400 : ℝ)) (96919 / 25000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (543 / 800 : ℝ) (492853 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (543 / 800 : ℝ))) h 2
    have he :
        (Real.exp (543 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (543 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (96919 / 25000 : ℝ) - (543 / 800 : ℝ) / 2) / 32)
      (72372371 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_543 :
    ∀ u : ℝ, (543 / 800 : ℝ) ≤ u → u ≤ (17 / 25 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (373753 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (543 / 800 : ℝ) (17 / 25 : ℝ) (60726 / 15625 : ℝ) (974048589721 / 250000000000 : ℝ)
    (36219951 / 25000000 : ℝ) (70429 / 10000000000 : ℝ) (373753 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (543 / 800 : ℝ)) (60726 / 15625 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (17 / 25 : ℝ) (986939 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (17 / 25 : ℝ))) h 2
    have he :
        (Real.exp (17 / 25 : ℝ)) ^ 2 =
          Real.exp (2 * (17 / 25 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (60726 / 15625 : ℝ) - (17 / 25 : ℝ) / 2) / 32)
      (36219951 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_544 :
    ∀ u : ℝ, (17 / 25 : ℝ) ≤ u → u ≤ (109 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (729361 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (17 / 25 : ℝ) (109 / 160 : ℝ) (3896193 / 1000000 : ℝ) (3905947464409 / 1000000000000 : ℝ)
    (145015349 / 100000000 : ℝ) (68353 / 10000000000 : ℝ) (729361 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (17 / 25 : ℝ)) (3896193 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (109 / 160 : ℝ) (1976347 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (109 / 160 : ℝ))) h 2
    have he :
        (Real.exp (109 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (109 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3896193 / 1000000 : ℝ) - (109 / 160 : ℝ) / 2) / 32)
      (145015349 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_545 :
    ∀ u : ℝ, (109 / 160 : ℝ) ≤ u → u ≤ (273 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (711599 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (109 / 160 : ℝ) (273 / 400 : ℝ) (781189 / 200000 : ℝ) (3915724634761 / 1000000000000 : ℝ)
    (145151347 / 100000000 : ℝ) (66333 / 10000000000 : ℝ) (711599 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (109 / 160 : ℝ)) (781189 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (273 / 400 : ℝ) (1978819 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (273 / 400 : ℝ))) h 2
    have he :
        (Real.exp (273 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (273 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (781189 / 200000 : ℝ) - (273 / 400 : ℝ) / 2) / 32)
      (145151347 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_546 :
    ∀ u : ℝ, (273 / 400 : ℝ) ≤ u → u ≤ (547 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (694219 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (273 / 400 : ℝ) (547 / 800 : ℝ) (1957861 / 500000 : ℝ) (981381478609 / 250000000000 : ℝ)
    (14528783 / 10000000 : ℝ) (4023 / 625000000 : ℝ) (694219 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (273 / 400 : ℝ)) (1957861 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (547 / 800 : ℝ) (990647 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (547 / 800 : ℝ))) h 2
    have he :
        (Real.exp (547 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (547 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1957861 / 500000 : ℝ) - (547 / 800 : ℝ) / 2) / 32)
      (14528783 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_547 :
    ∀ u : ℝ, (547 / 800 : ℝ) ≤ u → u ≤ (137 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (338603 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (547 / 800 : ℝ) (137 / 200 : ℝ) (981381 / 250000 : ℝ) (245959459249 / 62500000000 : ℝ)
    (72712399 / 50000000 : ℝ) (7807 / 1250000000 : ℝ) (338603 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (547 / 800 : ℝ)) (981381 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (137 / 200 : ℝ) (495943 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (137 / 200 : ℝ))) h 2
    have he :
        (Real.exp (137 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (137 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (981381 / 250000 : ℝ) - (137 / 200 : ℝ) / 2) / 32)
      (72712399 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_548 :
    ∀ u : ℝ, (137 / 200 : ℝ) ≤ u → u ≤ (549 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (330279 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (137 / 200 : ℝ) (549 / 800 : ℝ) (78707 / 20000 : ℝ) (986301238129 / 250000000000 : ℝ)
    (72781119 / 50000000 : ℝ) (15149 / 2500000000 : ℝ) (330279 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (137 / 200 : ℝ)) (78707 / 20000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (549 / 800 : ℝ) (993127 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (549 / 800 : ℝ))) h 2
    have he :
        (Real.exp (549 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (549 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (78707 / 20000 : ℝ) - (549 / 800 : ℝ) / 2) / 32)
      (72781119 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_549 :
    ∀ u : ℝ, (549 / 800 : ℝ) ≤ u → u ≤ (11 / 16 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (644269 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (549 / 800 : ℝ) (11 / 16 : ℝ) (3945201 / 1000000 : ℝ) (988769708161 / 250000000000 : ℝ)
    (29140033 / 20000000 : ℝ) (58787 / 10000000000 : ℝ) (644269 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (549 / 800 : ℝ)) (3945201 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (11 / 16 : ℝ) (994369 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (11 / 16 : ℝ))) h 2
    have he :
        (Real.exp (11 / 16 : ℝ)) ^ 2 =
          Real.exp (2 * (11 / 16 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3945201 / 1000000 : ℝ) - (11 / 16 : ℝ) / 2) / 32)
      (29140033 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_550 :
    ∀ u : ℝ, (11 / 16 : ℝ) ≤ u → u ≤ (551 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (628337 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (11 / 16 : ℝ) (551 / 800 : ℝ) (988769 / 250000 : ℝ) (6343963201 / 1600000000 : ℝ)
    (72919283 / 50000000 : ℝ) (14257 / 2500000000 : ℝ) (628337 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (11 / 16 : ℝ)) (988769 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (551 / 800 : ℝ) (79649 / 40000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (551 / 800 : ℝ))) h 2
    have he :
        (Real.exp (551 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (551 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (988769 / 250000 : ℝ) - (551 / 800 : ℝ) / 2) / 32)
      (72919283 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_551 :
    ∀ u : ℝ, (551 / 800 : ℝ) ≤ u → u ≤ (69 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (153187 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (551 / 800 : ℝ) (69 / 100 : ℝ) (247811 / 62500 : ℝ) (248431468041 / 62500000000 : ℝ)
    (145977457 / 100000000 : ℝ) (55317 / 10000000000 : ℝ) (153187 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (551 / 800 : ℝ)) (247811 / 62500 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (69 / 100 : ℝ) (498429 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (69 / 100 : ℝ))) h 2
    have he :
        (Real.exp (69 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (69 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (247811 / 62500 : ℝ) - (69 / 100 : ℝ) / 2) / 32)
      (145977457 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_552 :
    ∀ u : ℝ, (69 / 100 : ℝ) ≤ u → u ≤ (553 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (597497 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (69 / 100 : ℝ) (553 / 800 : ℝ) (3974901 / 1000000 : ℝ) (39848543641 / 10000000000 : ℝ)
    (73058419 / 50000000 : ℝ) (53653 / 10000000000 : ℝ) (597497 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (69 / 100 : ℝ)) (3974901 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (553 / 800 : ℝ) (199621 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (553 / 800 : ℝ))) h 2
    have he :
        (Real.exp (553 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (553 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3974901 / 1000000 : ℝ) - (553 / 800 : ℝ) / 2) / 32)
      (73058419 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_553 :
    ∀ u : ℝ, (553 / 800 : ℝ) ≤ u → u ≤ (277 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (582579 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (553 / 800 : ℝ) (277 / 400 : ℝ) (3984851 / 1000000 : ℝ) (3994829671849 / 1000000000000 : ℝ)
    (146256711 / 100000000 : ℝ) (10407 / 2000000000 : ℝ) (582579 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (553 / 800 : ℝ)) (3984851 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (277 / 400 : ℝ) (1998707 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (277 / 400 : ℝ))) h 2
    have he :
        (Real.exp (277 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (277 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3984851 / 1000000 : ℝ) - (277 / 400 : ℝ) / 2) / 32)
      (146256711 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_554 :
    ∀ u : ℝ, (277 / 400 : ℝ) ≤ u → u ≤ (111 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (567991 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (277 / 400 : ℝ) (111 / 160 : ℝ) (159793 / 40000 : ℝ) (4004829456849 / 1000000000000 : ℝ)
    (146397063 / 100000000 : ℝ) (25231 / 5000000000 : ℝ) (567991 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (277 / 400 : ℝ)) (159793 / 40000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (111 / 160 : ℝ) (2001207 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (111 / 160 : ℝ))) h 2
    have he :
        (Real.exp (111 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (111 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (159793 / 40000 : ℝ) - (111 / 160 : ℝ) / 2) / 32)
      (146397063 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_555 :
    ∀ u : ℝ, (111 / 160 : ℝ) ≤ u → u ≤ (139 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (553727 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (111 / 160 : ℝ) (139 / 200 : ℝ) (160193 / 40000 : ℝ) (40148537641 / 10000000000 : ℝ)
    (36634481 / 25000000 : ℝ) (48933 / 10000000000 : ℝ) (553727 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (111 / 160 : ℝ)) (160193 / 40000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (139 / 200 : ℝ) (200371 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (139 / 200 : ℝ))) h 2
    have he :
        (Real.exp (139 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (139 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (160193 / 40000 : ℝ) - (139 / 200 : ℝ) / 2) / 32)
      (36634481 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_556 :
    ∀ u : ℝ, (139 / 200 : ℝ) ≤ u → u ≤ (557 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (269891 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (139 / 200 : ℝ) (557 / 800 : ℝ) (4014849 / 1000000 : ℝ) (62889103729 / 15625000000 : ℝ)
    (29335853 / 20000000 : ℝ) (47447 / 10000000000 : ℝ) (269891 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (139 / 200 : ℝ)) (4014849 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (557 / 800 : ℝ) (250777 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (557 / 800 : ℝ))) h 2
    have he :
        (Real.exp (557 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (557 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4014849 / 1000000 : ℝ) - (557 / 800 : ℝ) / 2) / 32)
      (29335853 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_557 :
    ∀ u : ℝ, (557 / 800 : ℝ) ≤ u → u ≤ (279 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (52613 / 10000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (557 / 800 : ℝ) (279 / 400 : ℝ) (4024899 / 1000000 : ℝ) (6455961801 / 1600000000 : ℝ)
    (73410559 / 50000000 : ℝ) (46001 / 10000000000 : ℝ) (52613 / 10000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (557 / 800 : ℝ)) (4024899 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (279 / 400 : ℝ) (80349 / 40000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (279 / 400 : ℝ))) h 2
    have he :
        (Real.exp (279 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (279 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4024899 / 1000000 : ℝ) - (279 / 400 : ℝ) / 2) / 32)
      (73410559 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_558 :
    ∀ u : ℝ, (279 / 400 : ℝ) ≤ u → u ≤ (559 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (512799 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (279 / 400 : ℝ) (559 / 800 : ℝ) (2017487 / 500000 : ℝ) (1011269573161 / 250000000000 : ℝ)
    (36740867 / 25000000 : ℝ) (44597 / 10000000000 : ℝ) (512799 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (279 / 400 : ℝ)) (2017487 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (559 / 800 : ℝ) (1005619 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (559 / 800 : ℝ))) h 2
    have he :
        (Real.exp (559 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (559 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2017487 / 500000 : ℝ) - (559 / 800 : ℝ) / 2) / 32)
      (36740867 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_559 :
    ∀ u : ℝ, (559 / 800 : ℝ) ≤ u → u ≤ (7 / 10 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (6247 / 1250000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (559 / 800 : ℝ) (7 / 10 : ℝ) (2022537 / 500000 : ℝ) (4055201145009 / 1000000000000 : ℝ)
    (147106317 / 100000000 : ℝ) (1351 / 312500000 : ℝ) (6247 / 1250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (559 / 800 : ℝ)) (2022537 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (7 / 10 : ℝ) (2013753 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (7 / 10 : ℝ))) h 2
    have he :
        (Real.exp (7 / 10 : ℝ)) ^ 2 =
          Real.exp (2 * (7 / 10 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2022537 / 500000 : ℝ) - (7 / 10 : ℝ) / 2) / 32)
      (147106317 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_540
#print axioms hpThetaEnergyUpper_interval_559

end HodgeProofHP
