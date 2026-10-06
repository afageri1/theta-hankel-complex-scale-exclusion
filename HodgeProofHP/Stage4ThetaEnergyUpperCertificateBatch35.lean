import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_700 :
    ∀ u : ℝ, (7 / 8 : ℝ) ≤ u → u ≤ (701 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2687 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (7 / 8 : ℝ) (701 / 800 : ℝ) (28773 / 5000 : ℝ) (360563019961 / 62500000000 : ℝ)
    (173495021 / 100000000 : ℝ) (221 / 10000000000 : ℝ) (2687 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (7 / 8 : ℝ)) (28773 / 5000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (701 / 800 : ℝ) (600469 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (701 / 800 : ℝ))) h 2
    have he :
        (Real.exp (701 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (701 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (28773 / 5000 : ℝ) - (701 / 800 : ℝ) / 2) / 32)
      (173495021 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_701 :
    ∀ u : ℝ, (701 / 800 : ℝ) ≤ u → u ≤ (351 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2579 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (701 / 800 : ℝ) (351 / 400 : ℝ) (1153801 / 200000 : ℝ) (903663721 / 156250000 : ℝ)
    (34747407 / 20000000 : ℝ) (211 / 10000000000 : ℝ) (2579 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (701 / 800 : ℝ)) (1153801 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (351 / 400 : ℝ) (30061 / 12500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (351 / 400 : ℝ))) h 2
    have he :
        (Real.exp (351 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (351 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1153801 / 200000 : ℝ) - (351 / 400 : ℝ) / 2) / 32)
      (34747407 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_702 :
    ∀ u : ℝ, (351 / 400 : ℝ) ≤ u → u ≤ (703 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1241 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (351 / 400 : ℝ) (703 / 800 : ℝ) (1156689 / 200000 : ℝ) (22648143049 / 3906250000 : ℝ)
    (173979983 / 100000000 : ℝ) (101 / 5000000000 : ℝ) (1241 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (351 / 400 : ℝ)) (1156689 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (703 / 800 : ℝ) (150493 / 62500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (703 / 800 : ℝ))) h 2
    have he :
        (Real.exp (703 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (703 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1156689 / 200000 : ℝ) - (703 / 800 : ℝ) / 2) / 32)
      (173979983 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_703 :
    ∀ u : ℝ, (703 / 800 : ℝ) ≤ u → u ≤ (22 / 25 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (4767 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (703 / 800 : ℝ) (22 / 25 : ℝ) (2898961 / 500000 : ℝ) (581243881 / 100000000 : ℝ)
    (5444497 / 3125000 : ℝ) (193 / 10000000000 : ℝ) (4767 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (703 / 800 : ℝ)) (2898961 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (22 / 25 : ℝ) (24109 / 10000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (22 / 25 : ℝ))) h 2
    have he :
        (Real.exp (22 / 25 : ℝ)) ^ 2 =
          Real.exp (2 * (22 / 25 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2898961 / 500000 : ℝ) - (22 / 25 : ℝ) / 2) / 32)
      (5444497 / 3125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_704 :
    ∀ u : ℝ, (22 / 25 : ℝ) ≤ u → u ≤ (141 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2297 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (22 / 25 : ℝ) (141 / 160 : ℝ) (1162487 / 200000 : ℝ) (364186903441 / 62500000000 : ℝ)
    (10904299 / 6250000 : ℝ) (37 / 2000000000 : ℝ) (2297 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (22 / 25 : ℝ)) (1162487 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (141 / 160 : ℝ) (603479 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (141 / 160 : ℝ))) h 2
    have he :
        (Real.exp (141 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (141 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1162487 / 200000 : ℝ) - (141 / 160 : ℝ) / 2) / 32)
      (10904299 / 6250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_705 :
    ∀ u : ℝ, (141 / 160 : ℝ) ≤ u → u ≤ (353 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (4393 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (141 / 160 : ℝ) (353 / 400 : ℝ) (728373 / 125000 : ℝ) (233662991769 / 40000000000 : ℝ)
    (682479 / 390625 : ℝ) (11 / 625000000 : ℝ) (4393 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (141 / 160 : ℝ)) (728373 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (353 / 400 : ℝ) (483387 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (353 / 400 : ℝ))) h 2
    have he :
        (Real.exp (353 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (353 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (728373 / 125000 : ℝ) - (353 / 400 : ℝ) / 2) / 32)
      (682479 / 390625 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_706 :
    ∀ u : ℝ, (353 / 400 : ℝ) ≤ u → u ≤ (707 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (53 / 1250000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (353 / 400 : ℝ) (707 / 800 : ℝ) (584157 / 100000 : ℝ) (1464049180441 / 250000000000 : ℝ)
    (174961447 / 100000000 : ℝ) (169 / 10000000000 : ℝ) (53 / 1250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (353 / 400 : ℝ)) (584157 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (707 / 800 : ℝ) (1209979 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (707 / 800 : ℝ))) h 2
    have he :
        (Real.exp (707 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (707 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (584157 / 100000 : ℝ) - (707 / 800 : ℝ) / 2) / 32)
      (174961447 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_707 :
    ∀ u : ℝ, (707 / 800 : ℝ) ≤ u → u ≤ (177 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (4061 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (707 / 800 : ℝ) (177 / 200 : ℝ) (91503 / 15625 : ℝ) (234834252409 / 40000000000 : ℝ)
    (175209237 / 100000000 : ℝ) (161 / 10000000000 : ℝ) (4061 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (707 / 800 : ℝ)) (91503 / 15625 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (177 / 200 : ℝ) (484597 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (177 / 200 : ℝ))) h 2
    have he :
        (Real.exp (177 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (177 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (91503 / 15625 : ℝ) - (177 / 200 : ℝ) / 2) / 32)
      (175209237 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_708 :
    ∀ u : ℝ, (177 / 200 : ℝ) ≤ u → u ≤ (709 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (781 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (177 / 200 : ℝ) (709 / 800 : ℝ) (5870851 / 1000000 : ℝ) (5747610969 / 976562500 : ℝ)
    (35091603 / 20000000 : ℝ) (77 / 5000000000 : ℝ) (781 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (177 / 200 : ℝ)) (5870851 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (709 / 800 : ℝ) (75813 / 31250 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (709 / 800 : ℝ))) h 2
    have he :
        (Real.exp (709 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (709 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (5870851 / 1000000 : ℝ) - (709 / 800 : ℝ) / 2) / 32)
      (35091603 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_709 :
    ∀ u : ℝ, (709 / 800 : ℝ) ≤ u → u ≤ (71 / 80 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (3747 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (709 / 800 : ℝ) (71 / 80 : ℝ) (2942773 / 500000 : ℝ) (2360113561 / 400000000 : ℝ)
    (87853883 / 50000000 : ℝ) (147 / 10000000000 : ℝ) (3747 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (709 / 800 : ℝ)) (2942773 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (71 / 80 : ℝ) (48581 / 20000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (71 / 80 : ℝ))) h 2
    have he :
        (Real.exp (71 / 80 : ℝ)) ^ 2 =
          Real.exp (2 * (71 / 80 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2942773 / 500000 : ℝ) - (71 / 80 : ℝ) / 2) / 32)
      (87853883 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_710 :
    ∀ u : ℝ, (71 / 80 : ℝ) ≤ u → u ≤ (711 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (3613 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (71 / 80 : ℝ) (711 / 800 : ℝ) (2950139 / 500000 : ℝ) (92422688121 / 15625000000 : ℝ)
    (175958513 / 100000000 : ℝ) (141 / 10000000000 : ℝ) (3613 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (71 / 80 : ℝ)) (2950139 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (711 / 800 : ℝ) (304011 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (711 / 800 : ℝ))) h 2
    have he :
        (Real.exp (711 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (711 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2950139 / 500000 : ℝ) - (711 / 800 : ℝ) / 2) / 32)
      (175958513 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_711 :
    ∀ u : ℝ, (711 / 800 : ℝ) ≤ u → u ≤ (89 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (3451 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (711 / 800 : ℝ) (89 / 100 : ℝ) (5915047 / 1000000 : ℝ) (59298581169 / 10000000000 : ℝ)
    (11013141 / 6250000 : ℝ) (67 / 5000000000 : ℝ) (3451 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (711 / 800 : ℝ)) (5915047 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (89 / 100 : ℝ) (243513 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (89 / 100 : ℝ))) h 2
    have he :
        (Real.exp (89 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (89 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (5915047 / 1000000 : ℝ) - (89 / 100 : ℝ) / 2) / 32)
      (11013141 / 6250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_712 :
    ∀ u : ℝ, (89 / 100 : ℝ) ≤ u → u ≤ (713 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1657 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (89 / 100 : ℝ) (713 / 800 : ℝ) (5929853 / 1000000 : ℝ) (5805373249 / 976562500 : ℝ)
    (176463001 / 100000000 : ℝ) (1 / 78125000 : ℝ) (1657 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (89 / 100 : ℝ)) (5929853 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (713 / 800 : ℝ) (76193 / 31250 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (713 / 800 : ℝ))) h 2
    have he :
        (Real.exp (713 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (713 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (5929853 / 1000000 : ℝ) - (713 / 800 : ℝ) / 2) / 32)
      (176463001 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_713 :
    ∀ u : ℝ, (713 / 800 : ℝ) ≤ u → u ≤ (357 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (3201 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (713 / 800 : ℝ) (357 / 400 : ℝ) (5944697 / 1000000 : ℝ) (1489896095769 / 250000000000 : ℝ)
    (176716767 / 100000000 : ℝ) (123 / 10000000000 : ℝ) (3201 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (713 / 800 : ℝ)) (5944697 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (357 / 400 : ℝ) (1220613 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (357 / 400 : ℝ))) h 2
    have he :
        (Real.exp (357 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (357 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (5944697 / 1000000 : ℝ) - (357 / 400 : ℝ) / 2) / 32)
      (176716767 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_714 :
    ∀ u : ℝ, (357 / 400 : ℝ) ≤ u → u ≤ (143 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (3061 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (357 / 400 : ℝ) (143 / 160 : ℝ) (5959577 / 1000000 : ℝ) (5974499829841 / 1000000000000 : ℝ)
    (176971523 / 100000000 : ℝ) (117 / 10000000000 : ℝ) (3061 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (357 / 400 : ℝ)) (5959577 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (143 / 160 : ℝ) (2444279 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (143 / 160 : ℝ))) h 2
    have he :
        (Real.exp (143 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (143 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (5959577 / 1000000 : ℝ) - (143 / 160 : ℝ) / 2) / 32)
      (176971523 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_715 :
    ∀ u : ℝ, (143 / 160 : ℝ) ≤ u → u ≤ (179 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (589 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (143 / 160 : ℝ) (179 / 200 : ℝ) (2987247 / 500000 : ℝ) (93585210889 / 15625000000 : ℝ)
    (17722729 / 10000000 : ℝ) (7 / 625000000 : ℝ) (589 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (143 / 160 : ℝ)) (2987247 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (179 / 200 : ℝ) (305917 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (179 / 200 : ℝ))) h 2
    have he :
        (Real.exp (179 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (179 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2987247 / 500000 : ℝ) - (179 / 200 : ℝ) / 2) / 32)
      (17722729 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_716 :
    ∀ u : ℝ, (179 / 200 : ℝ) ≤ u → u ≤ (717 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2829 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (179 / 200 : ℝ) (717 / 800 : ℝ) (5989449 / 1000000 : ℝ) (6004445457609 / 1000000000000 : ℝ)
    (22185511 / 12500000 : ℝ) (107 / 10000000000 : ℝ) (2829 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (179 / 200 : ℝ)) (5989449 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (717 / 800 : ℝ) (2450397 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (717 / 800 : ℝ))) h 2
    have he :
        (Real.exp (717 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (717 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (5989449 / 1000000 : ℝ) - (717 / 800 : ℝ) / 2) / 32)
      (22185511 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_717 :
    ∀ u : ℝ, (717 / 800 : ℝ) ≤ u → u ≤ (359 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2711 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (717 / 800 : ℝ) (359 / 400 : ℝ) (3002221 / 500000 : ℝ) (1504868946361 / 250000000000 : ℝ)
    (177741921 / 100000000 : ℝ) (51 / 5000000000 : ℝ) (2711 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (717 / 800 : ℝ)) (3002221 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (359 / 400 : ℝ) (1226731 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (359 / 400 : ℝ))) h 2
    have he :
        (Real.exp (359 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (359 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3002221 / 500000 : ℝ) - (359 / 400 : ℝ) / 2) / 32)
      (177741921 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_718 :
    ∀ u : ℝ, (359 / 400 : ℝ) ≤ u → u ≤ (719 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2591 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (359 / 400 : ℝ) (719 / 800 : ℝ) (376217 / 62500 : ℝ) (6034544553961 / 1000000000000 : ℝ)
    (7120031 / 4000000 : ℝ) (97 / 10000000000 : ℝ) (2591 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (359 / 400 : ℝ)) (376217 / 62500 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (719 / 800 : ℝ) (2456531 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (719 / 800 : ℝ))) h 2
    have he :
        (Real.exp (719 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (719 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (376217 / 62500 : ℝ) - (719 / 800 : ℝ) / 2) / 32)
      (7120031 / 4000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_719 :
    ∀ u : ℝ, (719 / 800 : ℝ) ≤ u → u ≤ (9 / 10 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2497 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (719 / 800 : ℝ) (9 / 10 : ℝ) (6034539 / 1000000 : ℝ) (378103239801 / 62500000000 : ℝ)
    (178260653 / 100000000 : ℝ) (93 / 10000000000 : ℝ) (2497 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (719 / 800 : ℝ)) (6034539 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (9 / 10 : ℝ) (614901 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (9 / 10 : ℝ))) h 2
    have he :
        (Real.exp (9 / 10 : ℝ)) ^ 2 =
          Real.exp (2 * (9 / 10 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (6034539 / 1000000 : ℝ) - (9 / 10 : ℝ) / 2) / 32)
      (178260653 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_700
#print axioms hpThetaEnergyUpper_interval_719

end HodgeProofHP
