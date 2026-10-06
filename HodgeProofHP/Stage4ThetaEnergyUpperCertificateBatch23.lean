import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_460 :
    ∀ u : ℝ, (23 / 40 : ℝ) ≤ u → u ≤ (461 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (4465853 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (23 / 40 : ℝ) (461 / 800 : ℝ) (197387 / 62500 : ℝ) (791525164329 / 250000000000 : ℝ)
    (135106569 / 100000000 : ℝ) (658193 / 10000000000 : ℝ) (4465853 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (23 / 40 : ℝ)) (197387 / 62500 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (461 / 800 : ℝ) (889677 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (461 / 800 : ℝ))) h 2
    have he :
        (Real.exp (461 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (461 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (197387 / 62500 : ℝ) - (461 / 800 : ℝ) / 2) / 32)
      (135106569 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_461 :
    ∀ u : ℝ, (461 / 800 : ℝ) ≤ u → u ≤ (231 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1095711 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (461 / 800 : ℝ) (231 / 400 : ℝ) (1583049 / 500000 : ℝ) (3174023733241 / 1000000000000 : ℝ)
    (135208781 / 100000000 : ℝ) (80307 / 1250000000 : ℝ) (1095711 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (461 / 800 : ℝ)) (1583049 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (231 / 400 : ℝ) (1781579 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (231 / 400 : ℝ))) h 2
    have he :
        (Real.exp (231 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (231 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1583049 / 500000 : ℝ) - (231 / 400 : ℝ) / 2) / 32)
      (135208781 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_462 :
    ∀ u : ℝ, (231 / 400 : ℝ) ≤ u → u ≤ (463 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (430113 / 10000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (231 / 400 : ℝ) (463 / 800 : ℝ) (3174023 / 1000000 : ℝ) (776848384 / 244140625 : ℝ)
    (135311323 / 100000000 : ℝ) (313529 / 5000000000 : ℝ) (430113 / 10000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (231 / 400 : ℝ)) (3174023 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (463 / 800 : ℝ) (27872 / 15625 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (463 / 800 : ℝ))) h 2
    have he :
        (Real.exp (463 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (463 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3174023 / 1000000 : ℝ) - (463 / 800 : ℝ) / 2) / 32)
      (135311323 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_463 :
    ∀ u : ℝ, (463 / 800 : ℝ) ≤ u → u ≤ (29 / 50 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (527583 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (463 / 800 : ℝ) (29 / 50 : ℝ) (198873 / 62500 : ℝ) (3189935309521 / 1000000000000 : ℝ)
    (135414209 / 100000000 : ℝ) (611991 / 10000000000 : ℝ) (527583 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (463 / 800 : ℝ)) (198873 / 62500 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (29 / 50 : ℝ) (1786039 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (29 / 50 : ℝ))) h 2
    have he :
        (Real.exp (29 / 50 : ℝ)) ^ 2 =
          Real.exp (2 * (29 / 50 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (198873 / 62500 : ℝ) - (29 / 50 : ℝ) / 2) / 32)
      (135414209 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_464 :
    ∀ u : ℝ, (29 / 50 : ℝ) ≤ u → u ≤ (93 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1035359 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (29 / 50 : ℝ) (93 / 160 : ℝ) (3189933 / 1000000 : ℝ) (3197920322529 / 1000000000000 : ℝ)
    (67758719 / 50000000 : ℝ) (2333 / 39062500 : ℝ) (1035359 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (29 / 50 : ℝ)) (3189933 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (93 / 160 : ℝ) (1788273 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (93 / 160 : ℝ))) h 2
    have he :
        (Real.exp (93 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (93 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3189933 / 1000000 : ℝ) - (93 / 160 : ℝ) / 2) / 32)
      (67758719 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_465 :
    ∀ u : ℝ, (93 / 160 : ℝ) ≤ u → u ≤ (233 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (4063433 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (93 / 160 : ℝ) (233 / 400 : ℝ) (1598959 / 500000 : ℝ) (32059260601 / 10000000000 : ℝ)
    (135621013 / 100000000 : ℝ) (582823 / 10000000000 : ℝ) (4063433 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (93 / 160 : ℝ)) (1598959 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (233 / 400 : ℝ) (179051 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (233 / 400 : ℝ))) h 2
    have he :
        (Real.exp (233 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (233 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1598959 / 500000 : ℝ) - (233 / 400 : ℝ) / 2) / 32)
      (135621013 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_466 :
    ∀ u : ℝ, (233 / 400 : ℝ) ≤ u → u ≤ (467 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (996663 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (233 / 400 : ℝ) (467 / 800 : ℝ) (1602961 / 500000 : ℝ) (3213948977001 / 1000000000000 : ℝ)
    (135724919 / 100000000 : ℝ) (568713 / 10000000000 : ℝ) (996663 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (233 / 400 : ℝ)) (1602961 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (467 / 800 : ℝ) (1792749 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (467 / 800 : ℝ))) h 2
    have he :
        (Real.exp (467 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (467 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1602961 / 500000 : ℝ) - (467 / 800 : ℝ) / 2) / 32)
      (135724919 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_467 :
    ∀ u : ℝ, (467 / 800 : ℝ) ≤ u → u ≤ (117 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (3911061 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (467 / 800 : ℝ) (117 / 200 : ℝ) (3213947 / 1000000 : ℝ) (3221992690081 / 1000000000000 : ℝ)
    (27165837 / 20000000 : ℝ) (138727 / 2500000000 : ℝ) (3911061 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (467 / 800 : ℝ)) (3213947 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (117 / 200 : ℝ) (1794991 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (117 / 200 : ℝ))) h 2
    have he :
        (Real.exp (117 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (117 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3213947 / 1000000 : ℝ) - (117 / 200 : ℝ) / 2) / 32)
      (27165837 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_468 :
    ∀ u : ℝ, (117 / 200 : ℝ) ≤ u → u ≤ (469 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (153467 / 4000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (117 / 200 : ℝ) (469 / 800 : ℝ) (402749 / 125000 : ℝ) (3230060834169 / 1000000000000 : ℝ)
    (67966899 / 50000000 : ℝ) (108281 / 2000000000 : ℝ) (153467 / 4000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (117 / 200 : ℝ)) (402749 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (469 / 800 : ℝ) (1797237 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (469 / 800 : ℝ))) h 2
    have he :
        (Real.exp (469 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (469 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (402749 / 125000 : ℝ) - (469 / 800 : ℝ) / 2) / 32)
      (67966899 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_469 :
    ∀ u : ℝ, (469 / 800 : ℝ) ≤ u → u ≤ (47 / 80 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (752689 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (469 / 800 : ℝ) (47 / 80 : ℝ) (3230057 / 1000000 : ℝ) (129525850609 / 40000000000 : ℝ)
    (136038759 / 100000000 : ℝ) (132049 / 2500000000 : ℝ) (752689 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (469 / 800 : ℝ)) (3230057 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (47 / 80 : ℝ) (359897 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (47 / 80 : ℝ))) h 2
    have he :
        (Real.exp (47 / 80 : ℝ)) ^ 2 =
          Real.exp (2 * (47 / 80 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3230057 / 1000000 : ℝ) - (47 / 80 : ℝ) / 2) / 32)
      (136038759 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_470 :
    ∀ u : ℝ, (47 / 80 : ℝ) ≤ u → u ≤ (471 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (3691377 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (47 / 80 : ℝ) (471 / 800 : ℝ) (1619071 / 500000 : ℝ) (129849960409 / 40000000000 : ℝ)
    (34036017 / 25000000 : ℝ) (257639 / 5000000000 : ℝ) (3691377 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (47 / 80 : ℝ)) (1619071 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (471 / 800 : ℝ) (360347 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (471 / 800 : ℝ))) h 2
    have he :
        (Real.exp (471 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (471 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1619071 / 500000 : ℝ) - (471 / 800 : ℝ) / 2) / 32)
      (34036017 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_471 :
    ∀ u : ℝ, (471 / 800 : ℝ) ≤ u → u ≤ (59 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (3620451 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (471 / 800 : ℝ) (59 / 100 : ℝ) (405781 / 125000 : ℝ) (3254376312121 / 1000000000000 : ℝ)
    (136249739 / 100000000 : ℝ) (251321 / 5000000000 : ℝ) (3620451 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (471 / 800 : ℝ)) (405781 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (59 / 100 : ℝ) (1803989 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (59 / 100 : ℝ))) h 2
    have he :
        (Real.exp (59 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (59 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (405781 / 125000 : ℝ) - (59 / 100 : ℝ) / 2) / 32)
      (136249739 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_472 :
    ∀ u : ℝ, (59 / 100 : ℝ) ≤ u → u ≤ (473 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (887663 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (59 / 100 : ℝ) (473 / 800 : ℝ) (1627187 / 500000 : ℝ) (130500840001 / 40000000000 : ℝ)
    (1704447 / 1250000 : ℝ) (98057 / 2000000000 : ℝ) (887663 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (59 / 100 : ℝ)) (1627187 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (473 / 800 : ℝ) (361249 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (473 / 800 : ℝ))) h 2
    have he :
        (Real.exp (473 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (473 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1627187 / 500000 : ℝ) - (473 / 800 : ℝ) / 2) / 32)
      (1704447 / 1250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_473 :
    ∀ u : ℝ, (473 / 800 : ℝ) ≤ u → u ≤ (237 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (870497 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (473 / 800 : ℝ) (237 / 400 : ℝ) (81563 / 25000 : ℝ) (130827613401 / 40000000000 : ℝ)
    (136462131 / 100000000 : ℝ) (239101 / 5000000000 : ℝ) (870497 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (473 / 800 : ℝ)) (81563 / 25000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (237 / 400 : ℝ) (361701 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (237 / 400 : ℝ))) h 2
    have he :
        (Real.exp (237 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (237 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (81563 / 25000 : ℝ) - (237 / 400 : ℝ) / 2) / 32)
      (136462131 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_474 :
    ∀ u : ℝ, (237 / 400 : ℝ) ≤ u → u ≤ (19 / 32 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (341443 / 10000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (237 / 400 : ℝ) (19 / 32 : ℝ) (1635343 / 500000 : ℝ) (3278877128289 / 1000000000000 : ℝ)
    (136568853 / 100000000 : ℝ) (116597 / 2500000000 : ℝ) (341443 / 10000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (237 / 400 : ℝ)) (1635343 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (19 / 32 : ℝ) (1810767 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (19 / 32 : ℝ))) h 2
    have he :
        (Real.exp (19 / 32 : ℝ)) ^ 2 =
          Real.exp (2 * (19 / 32 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1635343 / 500000 : ℝ) - (19 / 32 : ℝ) / 2) / 32)
      (136568853 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_475 :
    ∀ u : ℝ, (19 / 32 : ℝ) ≤ u → u ≤ (119 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (418493 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (19 / 32 : ℝ) (119 / 200 : ℝ) (3278873 / 1000000 : ℝ) (3287081406961 / 1000000000000 : ℝ)
    (6833797 / 5000000 : ℝ) (90967 / 2000000000 : ℝ) (418493 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (19 / 32 : ℝ)) (3278873 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (119 / 200 : ℝ) (1813031 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (119 / 200 : ℝ))) h 2
    have he :
        (Real.exp (119 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (119 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3278873 / 1000000 : ℝ) - (119 / 200 : ℝ) / 2) / 32)
      (6833797 / 5000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_476 :
    ∀ u : ℝ, (119 / 200 : ℝ) ≤ u → u ≤ (477 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (65651 / 2000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (119 / 200 : ℝ) (477 / 800 : ℝ) (3287081 / 1000000 : ℝ) (3295310459401 / 1000000000000 : ℝ)
    (136783393 / 100000000 : ℝ) (22177 / 500000000 : ℝ) (65651 / 2000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (119 / 200 : ℝ)) (3287081 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (477 / 800 : ℝ) (1815299 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (477 / 800 : ℝ))) h 2
    have he :
        (Real.exp (477 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (477 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3287081 / 1000000 : ℝ) - (477 / 800 : ℝ) / 2) / 32)
      (136783393 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_477 :
    ∀ u : ℝ, (477 / 800 : ℝ) ≤ u → u ≤ (239 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1609113 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (477 / 800 : ℝ) (239 / 400 : ℝ) (3295309 / 1000000 : ℝ) (33035607049 / 10000000000 : ℝ)
    (136891199 / 100000000 : ℝ) (216249 / 5000000000 : ℝ) (1609113 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (477 / 800 : ℝ)) (3295309 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (239 / 400 : ℝ) (181757 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (239 / 400 : ℝ))) h 2
    have he :
        (Real.exp (239 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (239 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3295309 / 1000000 : ℝ) - (239 / 400 : ℝ) / 2) / 32)
      (136891199 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_478 :
    ∀ u : ℝ, (239 / 400 : ℝ) ≤ u → u ≤ (479 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (3154951 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (239 / 400 : ℝ) (479 / 800 : ℝ) (3303557 / 1000000 : ℝ) (3311828544649 / 1000000000000 : ℝ)
    (136999359 / 100000000 : ℝ) (52713 / 1250000000 : ℝ) (3154951 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (239 / 400 : ℝ)) (3303557 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (479 / 800 : ℝ) (1819843 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (479 / 800 : ℝ))) h 2
    have he :
        (Real.exp (479 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (479 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3303557 / 1000000 : ℝ) - (479 / 800 : ℝ) / 2) / 32)
      (136999359 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_479 :
    ∀ u : ℝ, (479 / 800 : ℝ) ≤ u → u ≤ (3 / 5 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (386589 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (479 / 800 : ℝ) (3 / 5 : ℝ) (1655913 / 500000 : ℝ) (3320117650161 / 1000000000000 : ℝ)
    (68553943 / 50000000 : ℝ) (25697 / 625000000 : ℝ) (386589 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (479 / 800 : ℝ)) (1655913 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (3 / 5 : ℝ) (1822119 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (3 / 5 : ℝ))) h 2
    have he :
        (Real.exp (3 / 5 : ℝ)) ^ 2 =
          Real.exp (2 * (3 / 5 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1655913 / 500000 : ℝ) - (3 / 5 : ℝ) / 2) / 32)
      (68553943 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_460
#print axioms hpThetaEnergyUpper_interval_479

end HodgeProofHP
