import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_300 :
    ∀ u : ℝ, (3 / 8 : ℝ) ≤ u → u ≤ (301 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (21806289 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (3 / 8 : ℝ) (301 / 800 : ℝ) (2117 / 1000 : ℝ) (132643825209 / 62500000000 : ℝ)
    (61183327 / 50000000 : ℝ) (15659623 / 10000000000 : ℝ) (21806289 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (3 / 8 : ℝ)) (2117 / 1000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (301 / 800 : ℝ) (364203 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (301 / 800 : ℝ))) h 2
    have he :
        (Real.exp (301 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (301 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2117 / 1000 : ℝ) - (301 / 800 : ℝ) / 2) / 32)
      (61183327 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_301 :
    ∀ u : ℝ, (301 / 800 : ℝ) ≤ u → u ≤ (151 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (21582887 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (301 / 800 : ℝ) (151 / 400 : ℝ) (2122299 / 1000000 : ℝ) (531903286489 / 250000000000 : ℝ)
    (61213953 / 50000000 : ℝ) (481589 / 312500000 : ℝ) (21582887 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (301 / 800 : ℝ)) (2122299 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (151 / 400 : ℝ) (729317 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (151 / 400 : ℝ))) h 2
    have he :
        (Real.exp (151 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (151 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2122299 / 1000000 : ℝ) - (151 / 400 : ℝ) / 2) / 32)
      (61213953 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_302 :
    ∀ u : ℝ, (151 / 400 : ℝ) ≤ u → u ≤ (303 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (21360831 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (151 / 400 : ℝ) (303 / 800 : ℝ) (2127611 / 1000000 : ℝ) (533234392441 / 250000000000 : ℝ)
    (24497869 / 20000000 : ℝ) (3033081 / 2000000000 : ℝ) (21360831 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (151 / 400 : ℝ)) (2127611 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (303 / 800 : ℝ) (730229 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (303 / 800 : ℝ))) h 2
    have he :
        (Real.exp (303 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (303 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2127611 / 1000000 : ℝ) - (303 / 800 : ℝ) / 2) / 32)
      (24497869 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_303 :
    ∀ u : ℝ, (303 / 800 : ℝ) ≤ u → u ≤ (19 / 50 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1057007 / 2500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (303 / 800 : ℝ) (19 / 50 : ℝ) (2132937 / 1000000 : ℝ) (85531096849 / 40000000000 : ℝ)
    (61275491 / 50000000 : ℝ) (746161 / 500000000 : ℝ) (1057007 / 2500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (303 / 800 : ℝ)) (2132937 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (19 / 50 : ℝ) (292457 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (19 / 50 : ℝ))) h 2
    have he :
        (Real.exp (19 / 50 : ℝ)) ^ 2 =
          Real.exp (2 * (19 / 50 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2132937 / 1000000 : ℝ) - (19 / 50 : ℝ) / 2) / 32)
      (61275491 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_304 :
    ∀ u : ℝ, (19 / 50 : ℝ) ≤ u → u ≤ (61 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (10460403 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (19 / 50 : ℝ) (61 / 160 : ℝ) (534569 / 250000 : ℝ) (535907451249 / 250000000000 : ℝ)
    (122612807 / 100000000 : ℝ) (7342151 / 5000000000 : ℝ) (10460403 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (19 / 50 : ℝ)) (534569 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (61 / 160 : ℝ) (732057 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (61 / 160 : ℝ))) h 2
    have he :
        (Real.exp (61 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (61 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (534569 / 250000 : ℝ) - (61 / 160 : ℝ) / 2) / 32)
      (122612807 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_305 :
    ∀ u : ℝ, (61 / 160 : ℝ) ≤ u → u ≤ (153 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1293927 / 3125000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (61 / 160 : ℝ) (153 / 400 : ℝ) (535907 / 250000 : ℝ) (85959789721 / 40000000000 : ℝ)
    (6133741 / 5000000 : ℝ) (14448617 / 10000000000 : ℝ) (1293927 / 3125000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (61 / 160 : ℝ)) (535907 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (153 / 400 : ℝ) (293189 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (153 / 400 : ℝ))) h 2
    have he :
        (Real.exp (153 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (153 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (535907 / 250000 : ℝ) - (153 / 400 : ℝ) / 2) / 32)
      (6133741 / 5000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_306 :
    ∀ u : ℝ, (153 / 400 : ℝ) ≤ u → u ≤ (307 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (40972463 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (153 / 400 : ℝ) (307 / 800 : ℝ) (1074497 / 500000 : ℝ) (2154375192841 / 1000000000000 : ℝ)
    (122737033 / 100000000 : ℝ) (1421609 / 1000000000 : ℝ) (40972463 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (153 / 400 : ℝ)) (1074497 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (307 / 800 : ℝ) (1467779 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (307 / 800 : ℝ))) h 2
    have he :
        (Real.exp (307 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (307 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1074497 / 500000 : ℝ) - (307 / 800 : ℝ) / 2) / 32)
      (122737033 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_307 :
    ∀ u : ℝ, (307 / 800 : ℝ) ≤ u → u ≤ (77 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (40542011 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (307 / 800 : ℝ) (77 / 200 : ℝ) (2154373 / 1000000 : ℝ) (86390729929 / 40000000000 : ℝ)
    (61399717 / 50000000 : ℝ) (2797347 / 2000000000 : ℝ) (40542011 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (307 / 800 : ℝ)) (2154373 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (77 / 200 : ℝ) (293923 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (77 / 200 : ℝ))) h 2
    have he :
        (Real.exp (77 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (77 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2154373 / 1000000 : ℝ) - (77 / 200 : ℝ) / 2) / 32)
      (61399717 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_308 :
    ∀ u : ℝ, (77 / 200 : ℝ) ≤ u → u ≤ (309 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (40114177 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (77 / 200 : ℝ) (309 / 800 : ℝ) (1079883 / 500000 : ℝ) (2165173931209 / 1000000000000 : ℝ)
    (30715509 / 25000000 : ℝ) (13760473 / 10000000000 : ℝ) (40114177 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (77 / 200 : ℝ)) (1079883 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (309 / 800 : ℝ) (1471453 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (309 / 800 : ℝ))) h 2
    have he :
        (Real.exp (309 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (309 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1079883 / 500000 : ℝ) - (309 / 800 : ℝ) / 2) / 32)
      (30715509 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_309 :
    ∀ u : ℝ, (309 / 800 : ℝ) ≤ u → u ≤ (31 / 80 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (248057 / 625000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (309 / 800 : ℝ) (31 / 80 : ℝ) (541293 / 250000 : ℝ) (2170592263849 / 1000000000000 : ℝ)
    (61462413 / 50000000 : ℝ) (6768661 / 5000000000 : ℝ) (248057 / 625000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (309 / 800 : ℝ)) (541293 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (31 / 80 : ℝ) (1473293 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (31 / 80 : ℝ))) h 2
    have he :
        (Real.exp (31 / 80 : ℝ)) ^ 2 =
          Real.exp (2 * (31 / 80 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (541293 / 250000 : ℝ) - (31 / 80 : ℝ) / 2) / 32)
      (61462413 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_310 :
    ∀ u : ℝ, (31 / 80 : ℝ) ≤ u → u ≤ (311 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (7853369 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (31 / 80 : ℝ) (311 / 800 : ℝ) (67831 / 31250 : ℝ) (531256401 / 244140625 : ℝ)
    (122987817 / 100000000 : ℝ) (3329301 / 2500000000 : ℝ) (7853369 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (31 / 80 : ℝ)) (67831 / 31250 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (311 / 800 : ℝ) (23049 / 15625 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (311 / 800 : ℝ))) h 2
    have he :
        (Real.exp (311 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (311 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (67831 / 31250 : ℝ) - (311 / 800 : ℝ) / 2) / 32)
      (122987817 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_311 :
    ∀ u : ℝ, (311 / 800 : ℝ) ≤ u → u ≤ (39 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (7769469 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (311 / 800 : ℝ) (39 / 100 : ℝ) (87041 / 40000 : ℝ) (2181472874361 / 1000000000000 : ℝ)
    (61525499 / 50000000 : ℝ) (409379 / 312500000 : ℝ) (7769469 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (311 / 800 : ℝ)) (87041 / 40000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (39 / 100 : ℝ) (1476981 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (39 / 100 : ℝ))) h 2
    have he :
        (Real.exp (39 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (39 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (87041 / 40000 : ℝ) - (39 / 100 : ℝ) / 2) / 32)
      (61525499 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_312 :
    ∀ u : ℝ, (39 / 100 : ℝ) ≤ u → u ≤ (313 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (19215323 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (39 / 100 : ℝ) (313 / 800 : ℝ) (68171 / 31250 : ℝ) (2186935211241 / 1000000000000 : ℝ)
    (6155719 / 5000000 : ℝ) (515441 / 400000000 : ℝ) (19215323 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (39 / 100 : ℝ)) (68171 / 31250 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (313 / 800 : ℝ) (1478829 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (313 / 800 : ℝ))) h 2
    have he :
        (Real.exp (313 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (313 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (68171 / 31250 : ℝ) - (313 / 800 : ℝ) / 2) / 32)
      (6155719 / 5000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_313 :
    ∀ u : ℝ, (313 / 800 : ℝ) ≤ u → u ≤ (157 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (9504153 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (313 / 800 : ℝ) (157 / 400 : ℝ) (546733 / 250000 : ℝ) (548101834921 / 250000000000 : ℝ)
    (3849311 / 3125000 : ℝ) (1584363 / 1250000000 : ℝ) (9504153 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (313 / 800 : ℝ)) (546733 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (157 / 400 : ℝ) (740339 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (157 / 400 : ℝ))) h 2
    have he :
        (Real.exp (157 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (157 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (546733 / 250000 : ℝ) - (157 / 400 : ℝ) / 2) / 32)
      (3849311 / 3125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_314 :
    ∀ u : ℝ, (157 / 400 : ℝ) ≤ u → u ≤ (63 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (37605391 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (157 / 400 : ℝ) (63 / 160 : ℝ) (1096203 / 500000 : ℝ) (21978952009 / 10000000000 : ℝ)
    (61620863 / 50000000 : ℝ) (6233347 / 5000000000 : ℝ) (37605391 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (157 / 400 : ℝ)) (1096203 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (63 / 160 : ℝ) (148253 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (63 / 160 : ℝ))) h 2
    have he :
        (Real.exp (63 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (63 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1096203 / 500000 : ℝ) - (63 / 160 : ℝ) / 2) / 32)
      (61620863 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_315 :
    ∀ u : ℝ, (63 / 160 : ℝ) ≤ u → u ≤ (79 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (37196993 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (63 / 160 : ℝ) (79 / 200 : ℝ) (1098947 / 500000 : ℝ) (88135953129 / 40000000000 : ℝ)
    (61652851 / 50000000 : ℝ) (12261367 / 10000000000 : ℝ) (37196993 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (63 / 160 : ℝ)) (1098947 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (79 / 200 : ℝ) (296877 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (79 / 200 : ℝ))) h 2
    have he :
        (Real.exp (79 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (79 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1098947 / 500000 : ℝ) - (79 / 200 : ℝ) / 2) / 32)
      (61652851 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_316 :
    ∀ u : ℝ, (79 / 200 : ℝ) ≤ u → u ≤ (317 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (18395581 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (79 / 200 : ℝ) (317 / 800 : ℝ) (550849 / 250000 : ℝ) (2208912310081 / 1000000000000 : ℝ)
    (123369881 / 100000000 : ℝ) (12058891 / 10000000000 : ℝ) (18395581 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (79 / 200 : ℝ)) (550849 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (317 / 800 : ℝ) (1486241 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (317 / 800 : ℝ))) h 2
    have he :
        (Real.exp (317 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (317 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (550849 / 250000 : ℝ) - (317 / 800 : ℝ) / 2) / 32)
      (123369881 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_317 :
    ∀ u : ℝ, (317 / 800 : ℝ) ≤ u → u ≤ (159 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (36388279 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (317 / 800 : ℝ) (159 / 400 : ℝ) (2208911 / 1000000 : ℝ) (221444161 / 100000000 : ℝ)
    (123434251 / 100000000 : ℝ) (11859273 / 10000000000 : ℝ) (36388279 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (317 / 800 : ℝ)) (2208911 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (159 / 400 : ℝ) (14881 / 10000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (159 / 400 : ℝ))) h 2
    have he :
        (Real.exp (159 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (159 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2208911 / 1000000 : ℝ) - (159 / 400 : ℝ) / 2) / 32)
      (123434251 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_318 :
    ∀ u : ℝ, (159 / 400 : ℝ) ≤ u → u ≤ (319 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (140579 / 390625 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (159 / 400 : ℝ) (319 / 800 : ℝ) (55361 / 25000 : ℝ) (554996690361 / 250000000000 : ℝ)
    (4939953 / 4000000 : ℝ) (2332489 / 2000000000 : ℝ) (140579 / 390625 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (159 / 400 : ℝ)) (55361 / 25000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (319 / 800 : ℝ) (744981 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (319 / 800 : ℝ))) h 2
    have he :
        (Real.exp (319 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (319 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (55361 / 25000 : ℝ) - (319 / 800 : ℝ) / 2) / 32)
      (4939953 / 4000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_319 :
    ∀ u : ℝ, (319 / 800 : ℝ) ≤ u → u ≤ (2 / 5 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (17795331 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (319 / 800 : ℝ) (2 / 5 : ℝ) (138749 / 62500 : ℝ) (3560866929 / 1600000000 : ℝ)
    (123563613 / 100000000 : ℝ) (2867087 / 2500000000 : ℝ) (17795331 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (319 / 800 : ℝ)) (138749 / 62500 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (2 / 5 : ℝ) (59673 / 40000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (2 / 5 : ℝ))) h 2
    have he :
        (Real.exp (2 / 5 : ℝ)) ^ 2 =
          Real.exp (2 * (2 / 5 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (138749 / 62500 : ℝ) - (2 / 5 : ℝ) / 2) / 32)
      (123563613 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_300
#print axioms hpThetaEnergyUpper_interval_319

end HodgeProofHP
