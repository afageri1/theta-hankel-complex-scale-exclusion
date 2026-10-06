import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_620 :
    ∀ u : ℝ, (31 / 40 : ℝ) ≤ u → u ≤ (621 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (44269 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (31 / 40 : ℝ) (621 / 800 : ℝ) (4711469 / 1000000 : ℝ) (295204228929 / 62500000000 : ℝ)
    (39215019 / 25000000 : ℝ) (2771 / 5000000000 : ℝ) (44269 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (31 / 40 : ℝ)) (4711469 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (621 / 800 : ℝ) (543327 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (621 / 800 : ℝ))) h 2
    have he :
        (Real.exp (621 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (621 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4711469 / 1000000 : ℝ) - (621 / 800 : ℝ) / 2) / 32)
      (39215019 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_621 :
    ∀ u : ℝ, (621 / 800 : ℝ) ≤ u → u ≤ (311 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (85827 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (621 / 800 : ℝ) (311 / 400 : ℝ) (4723263 / 1000000 : ℝ) (1183772288169 / 250000000000 : ℝ)
    (78519323 / 50000000 : ℝ) (167 / 312500000 : ℝ) (85827 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (621 / 800 : ℝ)) (4723263 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (311 / 400 : ℝ) (1088013 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (311 / 400 : ℝ))) h 2
    have he :
        (Real.exp (311 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (311 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4723263 / 1000000 : ℝ) - (311 / 400 : ℝ) / 2) / 32)
      (78519323 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_622 :
    ∀ u : ℝ, (311 / 400 : ℝ) ≤ u → u ≤ (623 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (83181 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (311 / 400 : ℝ) (623 / 800 : ℝ) (2367543 / 500000 : ℝ) (296683927969 / 62500000000 : ℝ)
    (78608933 / 50000000 : ℝ) (161 / 312500000 : ℝ) (83181 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (311 / 400 : ℝ)) (2367543 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (623 / 800 : ℝ) (544687 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (623 / 800 : ℝ))) h 2
    have he :
        (Real.exp (623 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (623 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2367543 / 500000 : ℝ) - (623 / 800 : ℝ) / 2) / 32)
      (78608933 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_623 :
    ∀ u : ℝ, (623 / 800 : ℝ) ≤ u → u ≤ (39 / 50 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (40309 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (623 / 800 : ℝ) (39 / 50 : ℝ) (2373469 / 500000 : ℝ) (4758824449729 / 1000000000000 : ℝ)
    (157397739 / 100000000 : ℝ) (4967 / 10000000000 : ℝ) (40309 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (623 / 800 : ℝ)) (2373469 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (39 / 50 : ℝ) (2181473 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (39 / 50 : ℝ))) h 2
    have he :
        (Real.exp (39 / 50 : ℝ)) ^ 2 =
          Real.exp (2 * (39 / 50 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2373469 / 500000 : ℝ) - (39 / 50 : ℝ) / 2) / 32)
      (157397739 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_624 :
    ∀ u : ℝ, (39 / 50 : ℝ) ≤ u → u ≤ (25 / 32 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (19531 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (39 / 50 : ℝ) (25 / 32 : ℝ) (237941 / 50000 : ℝ) (4770734008401 / 1000000000000 : ℝ)
    (78789141 / 50000000 : ℝ) (1197 / 2500000000 : ℝ) (19531 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (39 / 50 : ℝ)) (237941 / 50000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (25 / 32 : ℝ) (2184201 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (25 / 32 : ℝ))) h 2
    have he :
        (Real.exp (25 / 32 : ℝ)) ^ 2 =
          Real.exp (2 * (25 / 32 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (237941 / 50000 : ℝ) - (25 / 32 : ℝ) / 2) / 32)
      (78789141 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_625 :
    ∀ u : ℝ, (25 / 32 : ℝ) ≤ u → u ≤ (313 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (757 / 1000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (25 / 32 : ℝ) (313 / 400 : ℝ) (1192683 / 250000 : ℝ) (4782675946489 / 1000000000000 : ℝ)
    (19719937 / 12500000 : ℝ) (923 / 2000000000 : ℝ) (757 / 1000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (25 / 32 : ℝ)) (1192683 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (313 / 400 : ℝ) (2186933 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (313 / 400 : ℝ))) h 2
    have he :
        (Real.exp (313 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (313 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1192683 / 250000 : ℝ) - (313 / 400 : ℝ) / 2) / 32)
      (19719937 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_626 :
    ∀ u : ℝ, (313 / 400 : ℝ) ≤ u → u ≤ (627 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (36673 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (313 / 400 : ℝ) (627 / 800 : ℝ) (2391337 / 500000 : ℝ) (4794650329561 / 1000000000000 : ℝ)
    (19742673 / 12500000 : ℝ) (139 / 312500000 : ℝ) (36673 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (313 / 400 : ℝ)) (2391337 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (627 / 800 : ℝ) (2189669 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (627 / 800 : ℝ))) h 2
    have he :
        (Real.exp (627 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (627 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2391337 / 500000 : ℝ) - (627 / 800 : ℝ) / 2) / 32)
      (19742673 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_627 :
    ∀ u : ℝ, (627 / 800 : ℝ) ≤ u → u ≤ (157 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (14213 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (627 / 800 : ℝ) (157 / 200 : ℝ) (2397323 / 500000 : ℝ) (4806648453649 / 1000000000000 : ℝ)
    (79061973 / 50000000 : ℝ) (4287 / 10000000000 : ℝ) (14213 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (627 / 800 : ℝ)) (2397323 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (157 / 200 : ℝ) (2192407 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (157 / 200 : ℝ))) h 2
    have he :
        (Real.exp (157 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (157 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2397323 / 500000 : ℝ) - (157 / 200 : ℝ) / 2) / 32)
      (79061973 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_628 :
    ∀ u : ℝ, (157 / 200 : ℝ) ≤ u → u ≤ (629 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (68841 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (157 / 200 : ℝ) (629 / 800 : ℝ) (4806647 / 1000000 : ℝ) (1927473409 / 400000000 : ℝ)
    (158307171 / 100000000 : ℝ) (4131 / 10000000000 : ℝ) (68841 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (157 / 200 : ℝ)) (4806647 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (629 / 800 : ℝ) (43903 / 20000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (629 / 800 : ℝ))) h 2
    have he :
        (Real.exp (629 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (629 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4806647 / 1000000 : ℝ) - (629 / 800 : ℝ) / 2) / 32)
      (158307171 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_629 :
    ∀ u : ℝ, (629 / 800 : ℝ) ≤ u → u ≤ (63 / 80 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2667 / 4000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (629 / 800 : ℝ) (63 / 80 : ℝ) (4818679 / 1000000 : ℝ) (193229697241 / 40000000000 : ℝ)
    (158491089 / 100000000 : ℝ) (199 / 500000000 : ℝ) (2667 / 4000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (629 / 800 : ℝ)) (4818679 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (63 / 80 : ℝ) (439579 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (63 / 80 : ℝ))) h 2
    have he :
        (Real.exp (63 / 80 : ℝ)) ^ 2 =
          Real.exp (2 * (63 / 80 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4818679 / 1000000 : ℝ) - (63 / 80 : ℝ) / 2) / 32)
      (158491089 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_630 :
    ∀ u : ℝ, (63 / 80 : ℝ) ≤ u → u ≤ (631 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (32293 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (63 / 80 : ℝ) (631 / 800 : ℝ) (4830741 / 1000000 : ℝ) (302677125921 / 62500000000 : ℝ)
    (158675689 / 100000000 : ℝ) (767 / 2000000000 : ℝ) (32293 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (63 / 80 : ℝ)) (4830741 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (631 / 800 : ℝ) (550161 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (631 / 800 : ℝ))) h 2
    have he :
        (Real.exp (631 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (631 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4830741 / 1000000 : ℝ) - (631 / 800 : ℝ) / 2) / 32)
      (158675689 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_631 :
    ∀ u : ℝ, (631 / 800 : ℝ) ≤ u → u ≤ (79 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (3127 / 5000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (631 / 800 : ℝ) (79 / 100 : ℝ) (4842833 / 1000000 : ℝ) (4854958339609 / 1000000000000 : ℝ)
    (158860971 / 100000000 : ℝ) (1847 / 5000000000 : ℝ) (3127 / 5000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (631 / 800 : ℝ)) (4842833 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (79 / 100 : ℝ) (2203397 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (79 / 100 : ℝ))) h 2
    have he :
        (Real.exp (79 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (79 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4842833 / 1000000 : ℝ) - (79 / 100 : ℝ) / 2) / 32)
      (158860971 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_632 :
    ∀ u : ℝ, (79 / 100 : ℝ) ≤ u → u ≤ (633 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (15139 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (79 / 100 : ℝ) (633 / 800 : ℝ) (970991 / 200000 : ℝ) (4867111059409 / 1000000000000 : ℝ)
    (159046937 / 100000000 : ℝ) (1779 / 5000000000 : ℝ) (15139 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (79 / 100 : ℝ)) (970991 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (633 / 800 : ℝ) (2206153 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (633 / 800 : ℝ))) h 2
    have he :
        (Real.exp (633 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (633 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (970991 / 200000 : ℝ) - (633 / 800 : ℝ) / 2) / 32)
      (159046937 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_633 :
    ∀ u : ℝ, (633 / 800 : ℝ) ≤ u → u ≤ (317 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (29317 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (633 / 800 : ℝ) (317 / 400 : ℝ) (4867107 / 1000000 : ℝ) (19059735249 / 3906250000 : ℝ)
    (15923359 / 10000000 : ℝ) (3427 / 10000000000 : ℝ) (29317 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (633 / 800 : ℝ)) (4867107 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (317 / 400 : ℝ) (138057 / 62500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (317 / 400 : ℝ))) h 2
    have he :
        (Real.exp (317 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (317 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4867107 / 1000000 : ℝ) - (317 / 400 : ℝ) / 2) / 32)
      (15923359 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_634 :
    ∀ u : ℝ, (317 / 400 : ℝ) ≤ u → u ≤ (127 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (56777 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (317 / 400 : ℝ) (127 / 160 : ℝ) (487929 / 100000 : ℝ) (7826410089 / 1600000000 : ℝ)
    (159420947 / 100000000 : ℝ) (3301 / 10000000000 : ℝ) (56777 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (317 / 400 : ℝ)) (487929 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (127 / 160 : ℝ) (88467 / 40000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (127 / 160 : ℝ))) h 2
    have he :
        (Real.exp (127 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (127 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (487929 / 100000 : ℝ) - (127 / 160 : ℝ) / 2) / 32)
      (159420947 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_635 :
    ∀ u : ℝ, (127 / 160 : ℝ) ≤ u → u ≤ (159 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (54967 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (127 / 160 : ℝ) (159 / 200 : ℝ) (305719 / 62500 : ℝ) (4903748942481 / 1000000000000 : ℝ)
    (15960901 / 10000000 : ℝ) (3179 / 10000000000 : ℝ) (54967 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (127 / 160 : ℝ)) (305719 / 62500 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (159 / 200 : ℝ) (2214441 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (159 / 200 : ℝ))) h 2
    have he :
        (Real.exp (159 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (159 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (305719 / 62500 : ℝ) - (159 / 200 : ℝ) / 2) / 32)
      (15960901 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_636 :
    ∀ u : ℝ, (159 / 200 : ℝ) ≤ u → u ≤ (637 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (53207 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (159 / 200 : ℝ) (637 / 800 : ℝ) (1225937 / 250000 : ℝ) (4916024618521 / 1000000000000 : ℝ)
    (31959553 / 20000000 : ℝ) (3061 / 10000000000 : ℝ) (53207 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (159 / 200 : ℝ)) (1225937 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (637 / 800 : ℝ) (2217211 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (637 / 800 : ℝ))) h 2
    have he :
        (Real.exp (637 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (637 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1225937 / 250000 : ℝ) - (637 / 800 : ℝ) / 2) / 32)
      (31959553 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_637 :
    ∀ u : ℝ, (637 / 800 : ℝ) ≤ u → u ≤ (319 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (6437 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (637 / 800 : ℝ) (319 / 400 : ℝ) (4916023 / 1000000 : ℝ) (197133336009 / 40000000000 : ℝ)
    (15998723 / 10000000 : ℝ) (2947 / 10000000000 : ℝ) (6437 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (637 / 800 : ℝ)) (4916023 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (319 / 400 : ℝ) (443997 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (319 / 400 : ℝ))) h 2
    have he :
        (Real.exp (319 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (319 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4916023 / 1000000 : ℝ) - (319 / 400 : ℝ) / 2) / 32)
      (15998723 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_638 :
    ∀ u : ℝ, (319 / 400 : ℝ) ≤ u → u ≤ (639 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (9967 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (319 / 400 : ℝ) (639 / 800 : ℝ) (616041 / 125000 : ℝ) (4940666463121 / 1000000000000 : ℝ)
    (10011087 / 6250000 : ℝ) (2837 / 10000000000 : ℝ) (9967 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (319 / 400 : ℝ)) (616041 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (639 / 800 : ℝ) (2222761 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (639 / 800 : ℝ))) h 2
    have he :
        (Real.exp (639 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (639 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (616041 / 125000 : ℝ) - (639 / 800 : ℝ) / 2) / 32)
      (10011087 / 6250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_639 :
    ∀ u : ℝ, (639 / 800 : ℝ) ≤ u → u ≤ (4 / 5 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (24113 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (639 / 800 : ℝ) (4 / 5 : ℝ) (617583 / 125000 : ℝ) (4953032742681 / 1000000000000 : ℝ)
    (160368267 / 100000000 : ℝ) (2731 / 10000000000 : ℝ) (24113 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (639 / 800 : ℝ)) (617583 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (4 / 5 : ℝ) (2225541 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (4 / 5 : ℝ))) h 2
    have he :
        (Real.exp (4 / 5 : ℝ)) ^ 2 =
          Real.exp (2 * (4 / 5 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (617583 / 125000 : ℝ) - (4 / 5 : ℝ) / 2) / 32)
      (160368267 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_620
#print axioms hpThetaEnergyUpper_interval_639

end HodgeProofHP
