import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_180 :
    ∀ u : ℝ, (9 / 40 : ℝ) ≤ u → u ≤ (181 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (111870753 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (9 / 40 : ℝ) (181 / 800 : ℝ) (196039 / 125000 : ℝ) (15722401321 / 10000000000 : ℝ)
    (11622473 / 10000000 : ℝ) (20341667 / 2500000000 : ℝ) (111870753 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (9 / 40 : ℝ)) (196039 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (181 / 800 : ℝ) (125389 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (181 / 800 : ℝ))) h 2
    have he :
        (Real.exp (181 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (181 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (196039 / 125000 : ℝ) - (181 / 800 : ℝ) / 2) / 32)
      (11622473 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_181 :
    ∀ u : ℝ, (181 / 800 : ℝ) ≤ u → u ≤ (91 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (55621607 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (181 / 800 : ℝ) (91 / 400 : ℝ) (1572237 / 1000000 : ℝ) (394043697441 / 250000000000 : ℝ)
    (11626723 / 10000000 : ℝ) (80420279 / 10000000000 : ℝ) (55621607 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (181 / 800 : ℝ)) (1572237 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (91 / 400 : ℝ) (627729 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (91 / 400 : ℝ))) h 2
    have he :
        (Real.exp (91 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (91 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1572237 / 1000000 : ℝ) - (91 / 400 : ℝ) / 2) / 32)
      (11626723 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_182 :
    ∀ u : ℝ, (91 / 400 : ℝ) ≤ u → u ≤ (183 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (110614909 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (91 / 400 : ℝ) (183 / 800 : ℝ) (1576173 / 1000000 : ℝ) (98757462049 / 62500000000 : ℝ)
    (7269367 / 6250000 : ℝ) (79482133 / 10000000000 : ℝ) (110614909 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (91 / 400 : ℝ)) (1576173 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (183 / 800 : ℝ) (314257 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (183 / 800 : ℝ))) h 2
    have he :
        (Real.exp (183 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (183 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1576173 / 1000000 : ℝ) - (183 / 800 : ℝ) / 2) / 32)
      (7269367 / 6250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_183 :
    ∀ u : ℝ, (183 / 800 : ℝ) ≤ u → u ≤ (23 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (54993589 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (183 / 800 : ℝ) (23 / 100 : ℝ) (790059 / 500000 : ℝ) (1584076477201 / 1000000000000 : ℝ)
    (14544079 / 12500000 : ℝ) (78552719 / 10000000000 : ℝ) (54993589 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (183 / 800 : ℝ)) (790059 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (23 / 100 : ℝ) (1258601 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (23 / 100 : ℝ))) h 2
    have he :
        (Real.exp (23 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (23 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (790059 / 500000 : ℝ) - (23 / 100 : ℝ) / 2) / 32)
      (14544079 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_184 :
    ∀ u : ℝ, (23 / 100 : ℝ) ≤ u → u ≤ (37 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (4374347 / 4000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (23 / 100 : ℝ) (37 / 160 : ℝ) (1584073 / 1000000 : ℝ) (2540865649 / 1600000000 : ℝ)
    (58197761 / 50000000 : ℝ) (38815867 / 5000000000 : ℝ) (4374347 / 4000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (23 / 100 : ℝ)) (1584073 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (37 / 160 : ℝ) (50407 / 40000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (37 / 160 : ℝ))) h 2
    have he :
        (Real.exp (37 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (37 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1584073 / 1000000 : ℝ) - (37 / 160 : ℝ) / 2) / 32)
      (58197761 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_185 :
    ∀ u : ℝ, (37 / 160 : ℝ) ≤ u → u ≤ (93 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (21745919 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (37 / 160 : ℝ) (93 / 400 : ℝ) (1588039 / 1000000 : ℝ) (1592015586001 / 1000000000000 : ℝ)
    (116438553 / 100000000 : ℝ) (19179727 / 2500000000 : ℝ) (21745919 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (37 / 160 : ℝ)) (1588039 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (93 / 400 : ℝ) (1261751 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (93 / 400 : ℝ))) h 2
    have he :
        (Real.exp (93 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (93 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1588039 / 1000000 : ℝ) - (93 / 400 : ℝ) / 2) / 32)
      (116438553 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_186 :
    ∀ u : ℝ, (93 / 400 : ℝ) ≤ u → u ≤ (187 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (4324027 / 4000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (93 / 400 : ℝ) (187 / 800 : ℝ) (796007 / 500000 : ℝ) (1596000162241 / 1000000000000 : ℝ)
    (14560213 / 12500000 : ℝ) (37907323 / 5000000000 : ℝ) (4324027 / 4000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (93 / 400 : ℝ)) (796007 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (187 / 800 : ℝ) (1263329 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (187 / 800 : ℝ))) h 2
    have he :
        (Real.exp (187 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (187 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (796007 / 500000 : ℝ) - (187 / 800 : ℝ) / 2) / 32)
      (14560213 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_187 :
    ∀ u : ℝ, (187 / 800 : ℝ) ≤ u → u ≤ (47 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (107471667 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (187 / 800 : ℝ) (47 / 200 : ℝ) (1595999 / 1000000 : ℝ) (1599994778281 / 1000000000000 : ℝ)
    (14565623 / 12500000 : ℝ) (37459359 / 5000000000 : ℝ) (107471667 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (187 / 800 : ℝ)) (1595999 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (47 / 200 : ℝ) (1264909 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (47 / 200 : ℝ))) h 2
    have he :
        (Real.exp (47 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (47 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1595999 / 1000000 : ℝ) - (47 / 200 : ℝ) / 2) / 32)
      (14565623 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_188 :
    ∀ u : ℝ, (47 / 200 : ℝ) ≤ u → u ≤ (189 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (106842531 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (47 / 200 : ℝ) (189 / 800 : ℝ) (799997 / 500000 : ℝ) (1603999453081 / 1000000000000 : ℝ)
    (29142099 / 25000000 : ℝ) (37015511 / 5000000000 : ℝ) (106842531 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (47 / 200 : ℝ)) (799997 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (189 / 800 : ℝ) (1266491 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (189 / 800 : ℝ))) h 2
    have he :
        (Real.exp (189 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (189 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (799997 / 500000 : ℝ) - (189 / 800 : ℝ) / 2) / 32)
      (29142099 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_189 :
    ∀ u : ℝ, (189 / 800 : ℝ) ≤ u → u ≤ (19 / 80 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (53106703 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (189 / 800 : ℝ) (19 / 80 : ℝ) (1603999 / 1000000 : ℝ) (2572822729 / 1600000000 : ℝ)
    (116611937 / 100000000 : ℝ) (73151579 / 10000000000 : ℝ) (53106703 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (189 / 800 : ℝ)) (1603999 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (19 / 80 : ℝ) (50723 / 40000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (19 / 80 : ℝ))) h 2
    have he :
        (Real.exp (19 / 80 : ℝ)) ^ 2 =
          Real.exp (2 * (19 / 80 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1603999 / 1000000 : ℝ) - (19 / 80 : ℝ) / 2) / 32)
      (116611937 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_190 :
    ∀ u : ℝ, (19 / 80 : ℝ) ≤ u → u ≤ (191 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (105584723 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (19 / 80 : ℝ) (191 / 800 : ℝ) (804007 / 500000 : ℝ) (403010398561 / 250000000000 : ℝ)
    (11665561 / 10000000 : ℝ) (2258759 / 312500000 : ℝ) (105584723 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (19 / 80 : ℝ)) (804007 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (191 / 800 : ℝ) (634831 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (191 / 800 : ℝ))) h 2
    have he :
        (Real.exp (191 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (191 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (804007 / 500000 : ℝ) - (191 / 800 : ℝ) / 2) / 32)
      (11665561 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_191 :
    ∀ u : ℝ, (191 / 800 : ℝ) ≤ u → u ≤ (6 / 25 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (20991129 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (191 / 800 : ℝ) (6 / 25 : ℝ) (1612039 / 1000000 : ℝ) (1034289 / 640000 : ℝ)
    (116699413 / 100000000 : ℝ) (1428343 / 200000000 : ℝ) (20991129 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (191 / 800 : ℝ)) (1612039 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (6 / 25 : ℝ) (1017 / 800 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (6 / 25 : ℝ))) h 2
    have he :
        (Real.exp (6 / 25 : ℝ)) ^ 2 =
          Real.exp (2 * (6 / 25 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1612039 / 1000000 : ℝ) - (6 / 25 : ℝ) / 2) / 32)
      (116699413 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_192 :
    ∀ u : ℝ, (6 / 25 : ℝ) ≤ u → u ≤ (193 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (13040833 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (6 / 25 : ℝ) (193 / 800 : ℝ) (808037 / 500000 : ℝ) (1012576041 / 625000000 : ℝ)
    (116743347 / 100000000 : ℝ) (70562103 / 10000000000 : ℝ) (13040833 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (6 / 25 : ℝ)) (808037 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (193 / 800 : ℝ) (31821 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (193 / 800 : ℝ))) h 2
    have he :
        (Real.exp (193 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (193 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (808037 / 500000 : ℝ) - (193 / 800 : ℝ) / 2) / 32)
      (116743347 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_193 :
    ∀ u : ℝ, (193 / 800 : ℝ) ≤ u → u ≤ (97 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (51848901 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (193 / 800 : ℝ) (97 / 400 : ℝ) (1620119 / 1000000 : ℝ) (396527569 / 244140625 : ℝ)
    (116787413 / 100000000 : ℝ) (69715087 / 10000000000 : ℝ) (51848901 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (193 / 800 : ℝ)) (1620119 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (97 / 400 : ℝ) (19913 / 15625 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (97 / 400 : ℝ))) h 2
    have he :
        (Real.exp (97 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (97 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1620119 / 1000000 : ℝ) - (97 / 400 : ℝ) / 2) / 32)
      (116787413 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_194 :
    ∀ u : ℝ, (97 / 400 : ℝ) ≤ u → u ≤ (39 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (51534399 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (97 / 400 : ℝ) (39 / 160 : ℝ) (64967 / 40000 : ℝ) (407060588169 / 250000000000 : ℝ)
    (116831621 / 100000000 : ℝ) (34437937 / 5000000000 : ℝ) (51534399 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (97 / 400 : ℝ)) (64967 / 40000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (39 / 160 : ℝ) (638013 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (39 / 160 : ℝ))) h 2
    have he :
        (Real.exp (39 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (39 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (64967 / 40000 : ℝ) - (39 / 160 : ℝ) / 2) / 32)
      (116831621 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_195 :
    ∀ u : ℝ, (39 / 160 : ℝ) ≤ u → u ≤ (49 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (51220189 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (39 / 160 : ℝ) (49 / 200 : ℝ) (20353 / 12500 : ℝ) (408079493721 / 250000000000 : ℝ)
    (116875949 / 100000000 : ℝ) (1701121 / 250000000 : ℝ) (51220189 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (39 / 160 : ℝ)) (20353 / 12500 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (49 / 200 : ℝ) (638811 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (49 / 200 : ℝ))) h 2
    have he :
        (Real.exp (49 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (49 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (20353 / 12500 : ℝ) - (49 / 200 : ℝ) / 2) / 32)
      (116875949 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_196 :
    ∀ u : ℝ, (49 / 200 : ℝ) ≤ u → u ≤ (197 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (50905943 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (49 / 200 : ℝ) (197 / 800 : ℝ) (408079 / 250000 : ℝ) (4091009521 / 2500000000 : ℝ)
    (5846021 / 5000000 : ℝ) (67221511 / 10000000000 : ℝ) (50905943 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (49 / 200 : ℝ)) (408079 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (197 / 800 : ℝ) (63961 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (197 / 800 : ℝ))) h 2
    have he :
        (Real.exp (197 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (197 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (408079 / 250000 : ℝ) - (197 / 800 : ℝ) / 2) / 32)
      (5846021 / 5000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_197 :
    ∀ u : ℝ, (197 / 800 : ℝ) ≤ u → u ≤ (99 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (101183707 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (197 / 800 : ℝ) (99 / 400 : ℝ) (818201 / 500000 : ℝ) (4101249681 / 2500000000 : ℝ)
    (116965023 / 100000000 : ℝ) (66406053 / 10000000000 : ℝ) (101183707 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (197 / 800 : ℝ)) (818201 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (99 / 400 : ℝ) (64041 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (99 / 400 : ℝ))) h 2
    have he :
        (Real.exp (99 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (99 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (818201 / 500000 : ℝ) - (99 / 400 : ℝ) / 2) / 32)
      (116965023 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_198 :
    ∀ u : ℝ, (99 / 400 : ℝ) ≤ u → u ≤ (199 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (6284743 / 6250000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (99 / 400 : ℝ) (199 / 800 : ℝ) (820249 / 500000 : ℝ) (411151546521 / 250000000000 : ℝ)
    (58504879 / 50000000 : ℝ) (8199803 / 1250000000 : ℝ) (6284743 / 6250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (99 / 400 : ℝ)) (820249 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (199 / 800 : ℝ) (641211 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (199 / 800 : ℝ))) h 2
    have he :
        (Real.exp (199 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (199 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (820249 / 500000 : ℝ) - (199 / 800 : ℝ) / 2) / 32)
      (58504879 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_199 :
    ∀ u : ℝ, (199 / 800 : ℝ) ≤ u → u ≤ (1 / 4 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (19985701 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (199 / 800 : ℝ) (1 / 4 : ℝ) (411151 / 250000 : ℝ) (412180692169 / 250000000000 : ℝ)
    (3657957 / 3125000 : ℝ) (64798601 / 10000000000 : ℝ) (19985701 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (199 / 800 : ℝ)) (411151 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (1 / 4 : ℝ) (642013 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (1 / 4 : ℝ))) h 2
    have he :
        (Real.exp (1 / 4 : ℝ)) ^ 2 =
          Real.exp (2 * (1 / 4 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (411151 / 250000 : ℝ) - (1 / 4 : ℝ) / 2) / 32)
      (3657957 / 3125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_180
#print axioms hpThetaEnergyUpper_interval_199

end HodgeProofHP
