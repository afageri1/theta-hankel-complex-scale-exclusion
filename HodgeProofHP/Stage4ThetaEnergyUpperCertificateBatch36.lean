import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_720 :
    ∀ u : ℝ, (9 / 10 : ℝ) ≤ u → u ≤ (721 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1201 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (9 / 10 : ℝ) (721 / 800 : ℝ) (1512411 / 250000 : ℝ) (3790495489 / 625000000 : ℝ)
    (22315197 / 12500000 : ℝ) (89 / 10000000000 : ℝ) (1201 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (9 / 10 : ℝ)) (1512411 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (721 / 800 : ℝ) (61567 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (721 / 800 : ℝ))) h 2
    have he :
        (Real.exp (721 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (721 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1512411 / 250000 : ℝ) - (721 / 800 : ℝ) / 2) / 32)
      (22315197 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_721 :
    ∀ u : ℝ, (721 / 800 : ℝ) ≤ u → u ≤ (361 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2307 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (721 / 800 : ℝ) (361 / 400 : ℝ) (6064787 / 1000000 : ℝ) (237498921 / 39062500 : ℝ)
    (44695887 / 25000000 : ℝ) (17 / 2000000000 : ℝ) (2307 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (721 / 800 : ℝ)) (6064787 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (361 / 400 : ℝ) (15411 / 6250 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (361 / 400 : ℝ))) h 2
    have he :
        (Real.exp (361 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (361 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (6064787 / 1000000 : ℝ) - (361 / 400 : ℝ) / 2) / 32)
      (44695887 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_722 :
    ∀ u : ℝ, (361 / 400 : ℝ) ≤ u → u ≤ (723 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2209 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (361 / 400 : ℝ) (723 / 800 : ℝ) (189999 / 31250 : ℝ) (380949418521 / 62500000000 : ℝ)
    (44761643 / 25000000 : ℝ) (81 / 10000000000 : ℝ) (2209 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (361 / 400 : ℝ)) (189999 / 31250 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (723 / 800 : ℝ) (617211 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (723 / 800 : ℝ))) h 2
    have he :
        (Real.exp (723 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (723 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (189999 / 31250 : ℝ) - (723 / 800 : ℝ) / 2) / 32)
      (44761643 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_723 :
    ∀ u : ℝ, (723 / 800 : ℝ) ≤ u → u ≤ (181 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2111 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (723 / 800 : ℝ) (181 / 200 : ℝ) (6095187 / 1000000 : ℝ) (381902988289 / 62500000000 : ℝ)
    (179310651 / 100000000 : ℝ) (77 / 10000000000 : ℝ) (2111 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (723 / 800 : ℝ)) (6095187 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (181 / 200 : ℝ) (617983 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (181 / 200 : ℝ))) h 2
    have he :
        (Real.exp (181 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (181 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (6095187 / 1000000 : ℝ) - (181 / 200 : ℝ) / 2) / 32)
      (179310651 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_724 :
    ∀ u : ℝ, (181 / 200 : ℝ) ≤ u → u ≤ (29 / 32 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (51 / 2500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (181 / 200 : ℝ) (29 / 32 : ℝ) (1527611 / 250000 : ℝ) (23928686721 / 3906250000 : ℝ)
    (17957579 / 10000000 : ℝ) (37 / 5000000000 : ℝ) (51 / 2500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (181 / 200 : ℝ)) (1527611 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (29 / 32 : ℝ) (154689 / 62500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (29 / 32 : ℝ))) h 2
    have he :
        (Real.exp (29 / 32 : ℝ)) ^ 2 =
          Real.exp (2 * (29 / 32 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1527611 / 250000 : ℝ) - (29 / 32 : ℝ) / 2) / 32)
      (17957579 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_725 :
    ∀ u : ℝ, (29 / 32 : ℝ) ≤ u → u ≤ (363 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (97 / 5000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (29 / 32 : ℝ) (363 / 400 : ℝ) (6125739 / 1000000 : ℝ) (3838174209 / 625000000 : ℝ)
    (179841991 / 100000000 : ℝ) (7 / 1000000000 : ℝ) (97 / 5000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (29 / 32 : ℝ)) (6125739 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (363 / 400 : ℝ) (61953 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (363 / 400 : ℝ))) h 2
    have he :
        (Real.exp (363 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (363 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (6125739 / 1000000 : ℝ) - (363 / 400 : ℝ) / 2) / 32)
      (179841991 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_726 :
    ∀ u : ℝ, (363 / 400 : ℝ) ≤ u → u ≤ (727 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (933 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (363 / 400 : ℝ) (727 / 800 : ℝ) (6141073 / 1000000 : ℝ) (15391131721 / 2500000000 : ℝ)
    (7204371 / 4000000 : ℝ) (67 / 10000000000 : ℝ) (933 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (363 / 400 : ℝ)) (6141073 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (727 / 800 : ℝ) (124061 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (727 / 800 : ℝ))) h 2
    have he :
        (Real.exp (727 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (727 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (6141073 / 1000000 : ℝ) - (727 / 800 : ℝ) / 2) / 32)
      (7204371 / 4000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_727 :
    ∀ u : ℝ, (727 / 800 : ℝ) ≤ u → u ≤ (91 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (7 / 390625 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (727 / 800 : ℝ) (91 / 100 : ℝ) (1539111 / 250000 : ℝ) (6171860768329 / 1000000000000 : ℝ)
    (180377613 / 100000000 : ℝ) (1 / 156250000 : ℝ) (7 / 390625 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (727 / 800 : ℝ)) (1539111 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (91 / 100 : ℝ) (2484323 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (91 / 100 : ℝ))) h 2
    have he :
        (Real.exp (91 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (91 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1539111 / 250000 : ℝ) - (91 / 100 : ℝ) / 2) / 32)
      (180377613 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_728 :
    ∀ u : ℝ, (91 / 100 : ℝ) ≤ u → u ≤ (729 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1717 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (91 / 100 : ℝ) (729 / 800 : ℝ) (1234371 / 200000 : ℝ) (61873080049 / 10000000000 : ℝ)
    (90323529 / 50000000 : ℝ) (61 / 10000000000 : ℝ) (1717 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (91 / 100 : ℝ)) (1234371 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (729 / 800 : ℝ) (248743 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (729 / 800 : ℝ))) h 2
    have he :
        (Real.exp (729 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (729 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1234371 / 200000 : ℝ) - (729 / 800 : ℝ) / 2) / 32)
      (90323529 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_729 :
    ∀ u : ℝ, (729 / 800 : ℝ) ≤ u → u ≤ (73 / 80 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1641 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (729 / 800 : ℝ) (73 / 80 : ℝ) (773413 / 125000 : ℝ) (1550699863441 / 250000000000 : ℝ)
    (180917581 / 100000000 : ℝ) (29 / 5000000000 : ℝ) (1641 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (729 / 800 : ℝ)) (773413 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (73 / 80 : ℝ) (1245271 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (73 / 80 : ℝ))) h 2
    have he :
        (Real.exp (73 / 80 : ℝ)) ^ 2 =
          Real.exp (2 * (73 / 80 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (773413 / 125000 : ℝ) - (73 / 80 : ℝ) / 2) / 32)
      (180917581 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_730 :
    ∀ u : ℝ, (73 / 80 : ℝ) ≤ u → u ≤ (731 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (391 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (73 / 80 : ℝ) (731 / 800 : ℝ) (6202791 / 1000000 : ℝ) (6218325233649 / 1000000000000 : ℝ)
    (36237837 / 20000000 : ℝ) (11 / 2000000000 : ℝ) (391 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (73 / 80 : ℝ)) (6202791 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (731 / 800 : ℝ) (2493657 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (731 / 800 : ℝ))) h 2
    have he :
        (Real.exp (731 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (731 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (6202791 / 1000000 : ℝ) - (731 / 800 : ℝ) / 2) / 32)
      (36237837 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_731 :
    ∀ u : ℝ, (731 / 800 : ℝ) ≤ u → u ≤ (183 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (303 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (731 / 800 : ℝ) (183 / 200 : ℝ) (3109159 / 500000 : ℝ) (97404537409 / 15625000000 : ℝ)
    (181461909 / 100000000 : ℝ) (53 / 10000000000 : ℝ) (303 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (731 / 800 : ℝ)) (3109159 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (183 / 200 : ℝ) (312097 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (183 / 200 : ℝ))) h 2
    have he :
        (Real.exp (183 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (183 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3109159 / 500000 : ℝ) - (183 / 200 : ℝ) / 2) / 32)
      (181461909 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_732 :
    ∀ u : ℝ, (183 / 200 : ℝ) ≤ u → u ≤ (733 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1437 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (183 / 200 : ℝ) (733 / 800 : ℝ) (6233883 / 1000000 : ℝ) (6249495010201 / 1000000000000 : ℝ)
    (4543393 / 2500000 : ℝ) (1 / 200000000 : ℝ) (1437 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (183 / 200 : ℝ)) (6233883 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (733 / 800 : ℝ) (2499899 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (733 / 800 : ℝ))) h 2
    have he :
        (Real.exp (733 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (733 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (6233883 / 1000000 : ℝ) - (733 / 800 : ℝ) / 2) / 32)
      (4543393 / 2500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_733 :
    ∀ u : ℝ, (733 / 800 : ℝ) ≤ u → u ≤ (367 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1387 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (733 / 800 : ℝ) (367 / 400 : ℝ) (6249487 / 1000000 : ℝ) (10024214641 / 1600000000 : ℝ)
    (91005321 / 50000000 : ℝ) (3 / 625000000 : ℝ) (1387 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (733 / 800 : ℝ)) (6249487 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (367 / 400 : ℝ) (100121 / 40000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (367 / 400 : ℝ))) h 2
    have he :
        (Real.exp (367 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (367 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (6249487 / 1000000 : ℝ) - (367 / 400 : ℝ) / 2) / 32)
      (91005321 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_734 :
    ∀ u : ℝ, (367 / 400 : ℝ) ≤ u → u ≤ (147 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (167 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (367 / 400 : ℝ) (147 / 160 : ℝ) (626513 / 100000 : ℝ) (392551118521 / 62500000000 : ℝ)
    (182286677 / 100000000 : ℝ) (23 / 5000000000 : ℝ) (167 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (367 / 400 : ℝ)) (626513 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (147 / 160 : ℝ) (626539 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (147 / 160 : ℝ))) h 2
    have he :
        (Real.exp (147 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (147 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (626513 / 100000 : ℝ) - (147 / 160 : ℝ) / 2) / 32)
      (182286677 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_735 :
    ∀ u : ℝ, (147 / 160 : ℝ) ≤ u → u ≤ (23 / 25 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (321 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (147 / 160 : ℝ) (23 / 25 : ℝ) (1570203 / 250000 : ℝ) (6296541322681 / 1000000000000 : ℝ)
    (182563829 / 100000000 : ℝ) (11 / 2500000000 : ℝ) (321 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (147 / 160 : ℝ)) (1570203 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (23 / 25 : ℝ) (2509291 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (23 / 25 : ℝ))) h 2
    have he :
        (Real.exp (23 / 25 : ℝ)) ^ 2 =
          Real.exp (2 * (23 / 25 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1570203 / 250000 : ℝ) - (23 / 25 : ℝ) / 2) / 32)
      (182563829 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_736 :
    ∀ u : ℝ, (23 / 25 : ℝ) ≤ u → u ≤ (737 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1233 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (23 / 25 : ℝ) (737 / 800 : ℝ) (3148267 / 500000 : ℝ) (6312299480041 / 1000000000000 : ℝ)
    (4571053 / 2500000 : ℝ) (21 / 5000000000 : ℝ) (1233 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (23 / 25 : ℝ)) (3148267 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (737 / 800 : ℝ) (2512429 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (737 / 800 : ℝ))) h 2
    have he :
        (Real.exp (737 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (737 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3148267 / 500000 : ℝ) - (737 / 800 : ℝ) / 2) / 32)
      (4571053 / 2500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_737 :
    ∀ u : ℝ, (737 / 800 : ℝ) ≤ u → u ≤ (369 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (59 / 5000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (737 / 800 : ℝ) (369 / 400 : ℝ) (1262459 / 200000 : ℝ) (395506405449 / 62500000000 : ℝ)
    (183121537 / 100000000 : ℝ) (1 / 250000000 : ℝ) (59 / 5000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (737 / 800 : ℝ)) (1262459 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (369 / 400 : ℝ) (628893 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (369 / 400 : ℝ))) h 2
    have he :
        (Real.exp (369 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (369 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1262459 / 200000 : ℝ) - (369 / 400 : ℝ) / 2) / 32)
      (183121537 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_738 :
    ∀ u : ℝ, (369 / 400 : ℝ) ≤ u → u ≤ (739 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1127 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (369 / 400 : ℝ) (739 / 800 : ℝ) (197753 / 31250 : ℝ) (1585985090881 / 250000000000 : ℝ)
    (1834021 / 1000000 : ℝ) (19 / 5000000000 : ℝ) (1127 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (369 / 400 : ℝ)) (197753 / 31250 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (739 / 800 : ℝ) (1259359 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (739 / 800 : ℝ))) h 2
    have he :
        (Real.exp (739 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (739 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (197753 / 31250 : ℝ) - (739 / 800 : ℝ) / 2) / 32)
      (1834021 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_739 :
    ∀ u : ℝ, (739 / 800 : ℝ) ≤ u → u ≤ (37 / 40 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1073 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (739 / 800 : ℝ) (37 / 40 : ℝ) (1268787 / 200000 : ℝ) (6359823253161 / 1000000000000 : ℝ)
    (91841889 / 50000000 : ℝ) (9 / 2500000000 : ℝ) (1073 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (739 / 800 : ℝ)) (1268787 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (37 / 40 : ℝ) (2521869 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (37 / 40 : ℝ))) h 2
    have he :
        (Real.exp (37 / 40 : ℝ)) ^ 2 =
          Real.exp (2 * (37 / 40 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1268787 / 200000 : ℝ) - (37 / 40 : ℝ) / 2) / 32)
      (91841889 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_720
#print axioms hpThetaEnergyUpper_interval_739

end HodgeProofHP
