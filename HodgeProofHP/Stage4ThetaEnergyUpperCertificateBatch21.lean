import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_420 :
    ∀ u : ℝ, (21 / 40 : ℝ) ≤ u → u ≤ (421 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (899341 / 10000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (21 / 40 : ℝ) (421 / 800 : ℝ) (2857651 / 1000000 : ℝ) (716201686369 / 250000000000 : ℝ)
    (131282899 / 100000000 : ℝ) (32989 / 200000000 : ℝ) (899341 / 10000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (21 / 40 : ℝ)) (2857651 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (421 / 800 : ℝ) (846287 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (421 / 800 : ℝ))) h 2
    have he :
        (Real.exp (421 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (421 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2857651 / 1000000 : ℝ) - (421 / 800 : ℝ) / 2) / 32)
      (131282899 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_421 :
    ∀ u : ℝ, (421 / 800 : ℝ) ≤ u → u ≤ (211 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1769527 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (421 / 800 : ℝ) (211 / 400 : ℝ) (716201 / 250000 : ℝ) (2871977585481 / 1000000000000 : ℝ)
    (4105391 / 3125000 : ℝ) (1613823 / 10000000000 : ℝ) (1769527 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (421 / 800 : ℝ)) (716201 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (211 / 400 : ℝ) (1694691 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (211 / 400 : ℝ))) h 2
    have he :
        (Real.exp (211 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (211 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (716201 / 250000 : ℝ) - (211 / 400 : ℝ) / 2) / 32)
      (4105391 / 3125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_422 :
    ∀ u : ℝ, (211 / 400 : ℝ) ≤ u → u ≤ (423 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (271991 / 3125000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (211 / 400 : ℝ) (423 / 800 : ℝ) (114879 / 40000 : ℝ) (28791641761 / 10000000000 : ℝ)
    (131462417 / 100000000 : ℝ) (789439 / 5000000000 : ℝ) (271991 / 3125000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (211 / 400 : ℝ)) (114879 / 40000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (423 / 800 : ℝ) (169681 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (423 / 800 : ℝ))) h 2
    have he :
        (Real.exp (423 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (423 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (114879 / 40000 : ℝ) - (423 / 800 : ℝ) / 2) / 32)
      (131462417 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_423 :
    ∀ u : ℝ, (423 / 800 : ℝ) ≤ u → u ≤ (53 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (8561659 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (423 / 800 : ℝ) (53 / 100 : ℝ) (719791 / 250000 : ℝ) (2886373338489 / 1000000000000 : ℝ)
    (131552617 / 100000000 : ℝ) (1544601 / 10000000000 : ℝ) (8561659 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (423 / 800 : ℝ)) (719791 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (53 / 100 : ℝ) (1698933 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (53 / 100 : ℝ))) h 2
    have he :
        (Real.exp (53 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (53 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (719791 / 250000 : ℝ) - (53 / 100 : ℝ) / 2) / 32)
      (131552617 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_424 :
    ∀ u : ℝ, (53 / 100 : ℝ) ≤ u → u ≤ (17 / 32 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (168429 / 2000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (53 / 100 : ℝ) (17 / 32 : ℝ) (288637 / 100000 : ℝ) (723399579841 / 250000000000 : ℝ)
    (65821549 / 50000000 : ℝ) (377747 / 2500000000 : ℝ) (168429 / 2000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (53 / 100 : ℝ)) (288637 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (17 / 32 : ℝ) (850529 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (17 / 32 : ℝ))) h 2
    have he :
        (Real.exp (17 / 32 : ℝ)) ^ 2 =
          Real.exp (2 * (17 / 32 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (288637 / 100000 : ℝ) - (17 / 32 : ℝ) / 2) / 32)
      (65821549 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_425 :
    ∀ u : ℝ, (17 / 32 : ℝ) ≤ u → u ≤ (213 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (8283019 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (17 / 32 : ℝ) (213 / 400 : ℝ) (578719 / 200000 : ℝ) (116033565769 / 40000000000 : ℝ)
    (131733887 / 100000000 : ℝ) (1478019 / 10000000000 : ℝ) (8283019 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (17 / 32 : ℝ)) (578719 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (213 / 400 : ℝ) (340637 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (213 / 400 : ℝ))) h 2
    have he :
        (Real.exp (213 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (213 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (578719 / 200000 : ℝ) - (213 / 400 : ℝ) / 2) / 32)
      (131733887 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_426 :
    ∀ u : ℝ, (213 / 400 : ℝ) ≤ u → u ≤ (427 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (4073209 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (213 / 400 : ℝ) (427 / 800 : ℝ) (1450419 / 500000 : ℝ) (181756416241 / 62500000000 : ℝ)
    (131824971 / 100000000 : ℝ) (1445687 / 10000000000 : ℝ) (4073209 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (213 / 400 : ℝ)) (1450419 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (427 / 800 : ℝ) (426329 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (427 / 800 : ℝ))) h 2
    have he :
        (Real.exp (427 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (427 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1450419 / 500000 : ℝ) - (427 / 800 : ℝ) / 2) / 32)
      (131824971 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_427 :
    ∀ u : ℝ, (427 / 800 : ℝ) ≤ u → u ≤ (107 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (4005783 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (427 / 800 : ℝ) (107 / 200 : ℝ) (29081 / 10000 : ℝ) (2915382087601 / 1000000000000 : ℝ)
    (26383273 / 20000000 : ℝ) (706989 / 5000000000 : ℝ) (4005783 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (427 / 800 : ℝ)) (29081 / 10000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (107 / 200 : ℝ) (1707449 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (107 / 200 : ℝ))) h 2
    have he :
        (Real.exp (107 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (107 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (29081 / 10000 : ℝ) - (107 / 200 : ℝ) / 2) / 32)
      (26383273 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_428 :
    ∀ u : ℝ, (107 / 200 : ℝ) ≤ u → u ≤ (429 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (7878501 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (107 / 200 : ℝ) (429 / 800 : ℝ) (2915379 / 1000000 : ℝ) (11416708801 / 3906250000 : ℝ)
    (132008041 / 100000000 : ℝ) (1382891 / 10000000000 : ℝ) (7878501 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (107 / 200 : ℝ)) (2915379 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (429 / 800 : ℝ) (106849 / 62500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (429 / 800 : ℝ))) h 2
    have he :
        (Real.exp (429 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (429 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2915379 / 1000000 : ℝ) - (429 / 800 : ℝ) / 2) / 32)
      (132008041 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_429 :
    ∀ u : ℝ, (429 / 800 : ℝ) ≤ u → u ≤ (43 / 80 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (7747197 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (429 / 800 : ℝ) (43 / 80 : ℝ) (2922677 / 1000000 : ℝ) (2929995628729 / 1000000000000 : ℝ)
    (33025007 / 25000000 : ℝ) (676203 / 5000000000 : ℝ) (7747197 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (429 / 800 : ℝ)) (2922677 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (43 / 80 : ℝ) (1711723 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (43 / 80 : ℝ))) h 2
    have he :
        (Real.exp (43 / 80 : ℝ)) ^ 2 =
          Real.exp (2 * (43 / 80 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2922677 / 1000000 : ℝ) - (43 / 80 : ℝ) / 2) / 32)
      (33025007 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_430 :
    ∀ u : ℝ, (43 / 80 : ℝ) ≤ u → u ≤ (431 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (3808827 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (43 / 80 : ℝ) (431 / 800 : ℝ) (366249 / 125000 : ℝ) (45895778289 / 15625000000 : ℝ)
    (1321923 / 1000000 : ℝ) (1322523 / 10000000000 : ℝ) (3808827 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (43 / 80 : ℝ)) (366249 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (431 / 800 : ℝ) (214233 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (431 / 800 : ℝ))) h 2
    have he :
        (Real.exp (431 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (431 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (366249 / 125000 : ℝ) - (431 / 800 : ℝ) / 2) / 32)
      (1321923 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_431 :
    ∀ u : ℝ, (431 / 800 : ℝ) ≤ u → u ≤ (27 / 50 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (374489 / 5000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (431 / 800 : ℝ) (27 / 50 : ℝ) (2937327 / 1000000 : ℝ) (2944680024049 / 1000000000000 : ℝ)
    (26456979 / 20000000 : ℝ) (1293219 / 10000000000 : ℝ) (374489 / 5000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (431 / 800 : ℝ)) (2937327 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (27 / 50 : ℝ) (1716007 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (27 / 50 : ℝ))) h 2
    have he :
        (Real.exp (27 / 50 : ℝ)) ^ 2 =
          Real.exp (2 * (27 / 50 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2937327 / 1000000 : ℝ) - (27 / 50 : ℝ) / 2) / 32)
      (26456979 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_432 :
    ∀ u : ℝ, (27 / 50 : ℝ) ≤ u → u ≤ (433 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (920459 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (27 / 50 : ℝ) (433 / 800 : ℝ) (2944679 / 1000000 : ℝ) (738013291929 / 250000000000 : ℝ)
    (8273611 / 6250000 : ℝ) (79031 / 625000000 : ℝ) (920459 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (27 / 50 : ℝ)) (2944679 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (433 / 800 : ℝ) (859077 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (433 / 800 : ℝ))) h 2
    have he :
        (Real.exp (433 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (433 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2944679 / 1000000 : ℝ) - (433 / 800 : ℝ) / 2) / 32)
      (8273611 / 6250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_433 :
    ∀ u : ℝ, (433 / 800 : ℝ) ≤ u → u ≤ (217 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1809809 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (433 / 800 : ℝ) (217 / 400 : ℝ) (59041 / 20000 : ℝ) (2959442411809 / 1000000000000 : ℝ)
    (13247097 / 10000000 : ℝ) (618169 / 5000000000 : ℝ) (1809809 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (433 / 800 : ℝ)) (59041 / 20000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (217 / 400 : ℝ) (1720303 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (217 / 400 : ℝ))) h 2
    have he :
        (Real.exp (217 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (217 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (59041 / 20000 : ℝ) - (217 / 400 : ℝ) / 2) / 32)
      (13247097 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_434 :
    ∀ u : ℝ, (217 / 400 : ℝ) ≤ u → u ≤ (87 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (7116479 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (217 / 400 : ℝ) (87 / 160 : ℝ) (2959439 / 1000000 : ℝ) (741711945529 / 250000000000 : ℝ)
    (132564463 / 100000000 : ℝ) (1208739 / 10000000000 : ℝ) (7116479 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (217 / 400 : ℝ)) (2959439 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (87 / 160 : ℝ) (861227 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (87 / 160 : ℝ))) h 2
    have he :
        (Real.exp (87 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (87 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2959439 / 1000000 : ℝ) - (87 / 160 : ℝ) / 2) / 32)
      (132564463 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_435 :
    ∀ u : ℝ, (87 / 160 : ℝ) ≤ u → u ≤ (109 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (6995397 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (87 / 160 : ℝ) (109 / 200 : ℝ) (2966847 / 1000000 : ℝ) (2974276202881 / 1000000000000 : ℝ)
    (132658269 / 100000000 : ℝ) (236337 / 2000000000 : ℝ) (6995397 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (87 / 160 : ℝ)) (2966847 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (109 / 200 : ℝ) (1724609 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (109 / 200 : ℝ))) h 2
    have he :
        (Real.exp (109 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (109 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2966847 / 1000000 : ℝ) - (109 / 200 : ℝ) / 2) / 32)
      (132658269 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_436 :
    ∀ u : ℝ, (109 / 200 : ℝ) ≤ u → u ≤ (437 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1375189 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (109 / 200 : ℝ) (437 / 800 : ℝ) (1487137 / 500000 : ℝ) (745430204689 / 250000000000 : ℝ)
    (13275239 / 10000000 : ℝ) (36099 / 312500000 : ℝ) (1375189 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (109 / 200 : ℝ)) (1487137 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (437 / 800 : ℝ) (863383 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (437 / 800 : ℝ))) h 2
    have he :
        (Real.exp (437 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (437 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1487137 / 500000 : ℝ) - (437 / 800 : ℝ) / 2) / 32)
      (13275239 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_437 :
    ∀ u : ℝ, (437 / 800 : ℝ) ≤ u → u ≤ (219 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (3379073 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (437 / 800 : ℝ) (219 / 400 : ℝ) (2981719 / 1000000 : ℝ) (747296278369 / 250000000000 : ℝ)
    (33211703 / 25000000 : ℝ) (564591 / 5000000000 : ℝ) (3379073 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (437 / 800 : ℝ)) (2981719 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (219 / 400 : ℝ) (864463 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (219 / 400 : ℝ))) h 2
    have he :
        (Real.exp (219 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (219 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2981719 / 1000000 : ℝ) - (219 / 400 : ℝ) / 2) / 32)
      (33211703 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_438 :
    ∀ u : ℝ, (219 / 400 : ℝ) ≤ u → u ≤ (439 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (6641967 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (219 / 400 : ℝ) (439 / 800 : ℝ) (1494591 / 500000 : ℝ) (11705725249 / 3906250000 : ℝ)
    (26588307 / 20000000 : ℝ) (551859 / 5000000000 : ℝ) (6641967 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (219 / 400 : ℝ)) (1494591 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (439 / 800 : ℝ) (108193 / 62500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (439 / 800 : ℝ))) h 2
    have he :
        (Real.exp (439 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (439 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1494591 / 500000 : ℝ) - (439 / 800 : ℝ) / 2) / 32)
      (26588307 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_439 :
    ∀ u : ℝ, (439 / 800 : ℝ) ≤ u → u ≤ (11 / 20 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (652741 / 10000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (439 / 800 : ℝ) (11 / 20 : ℝ) (374583 / 125000 : ℝ) (751042357129 / 250000000000 : ℝ)
    (5321463 / 4000000 : ℝ) (269691 / 2500000000 : ℝ) (652741 / 10000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (439 / 800 : ℝ)) (374583 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (11 / 20 : ℝ) (866627 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (11 / 20 : ℝ))) h 2
    have he :
        (Real.exp (11 / 20 : ℝ)) ^ 2 =
          Real.exp (2 * (11 / 20 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (374583 / 125000 : ℝ) - (11 / 20 : ℝ) / 2) / 32)
      (5321463 / 4000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_420
#print axioms hpThetaEnergyUpper_interval_439

end HodgeProofHP
