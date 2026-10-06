import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_100 :
    ∀ u : ℝ, (1 / 8 : ℝ) ≤ u → u ≤ (101 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (157547601 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (1 / 8 : ℝ) (101 / 800 : ℝ) (51361 / 40000 : ℝ) (321810002089 / 250000000000 : ℝ)
    (113204111 / 100000000 : ℝ) (23622163 / 1250000000 : ℝ) (157547601 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (1 / 8 : ℝ)) (51361 / 40000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (101 / 800 : ℝ) (567283 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (101 / 800 : ℝ))) h 2
    have he :
        (Real.exp (101 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (101 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (51361 / 40000 : ℝ) - (101 / 800 : ℝ) / 2) / 32)
      (113204111 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_101 :
    ∀ u : ℝ, (101 / 800 : ℝ) ≤ u → u ≤ (51 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (9817077 / 6250000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (101 / 800 : ℝ) (51 / 400 : ℝ) (1287239 / 1000000 : ℝ) (51618476809 / 40000000000 : ℝ)
    (56618803 / 50000000 : ℝ) (93598367 / 5000000000 : ℝ) (9817077 / 6250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (101 / 800 : ℝ)) (1287239 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (51 / 400 : ℝ) (227197 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (51 / 400 : ℝ))) h 2
    have he :
        (Real.exp (51 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (51 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1287239 / 1000000 : ℝ) - (51 / 400 : ℝ) / 2) / 32)
      (56618803 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_102 :
    ∀ u : ℝ, (51 / 400 : ℝ) ≤ u → u ≤ (103 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (156595609 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (51 / 400 : ℝ) (103 / 800 : ℝ) (1290461 / 1000000 : ℝ) (323423102209 / 250000000000 : ℝ)
    (113271201 / 100000000 : ℝ) (185428221 / 10000000000 : ℝ) (156595609 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (51 / 400 : ℝ)) (1290461 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (103 / 800 : ℝ) (568703 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (103 / 800 : ℝ))) h 2
    have he :
        (Real.exp (103 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (103 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1290461 / 1000000 : ℝ) - (103 / 800 : ℝ) / 2) / 32)
      (113271201 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_103 :
    ∀ u : ℝ, (103 / 800 : ℝ) ≤ u → u ≤ (13 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (9757179 / 6250000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (103 / 800 : ℝ) (13 / 100 : ℝ) (1293691 / 1000000 : ℝ) (1296931491241 / 1000000000000 : ℝ)
    (56652447 / 50000000 : ℝ) (183671849 / 10000000000 : ℝ) (9757179 / 6250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (103 / 800 : ℝ)) (1293691 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (13 / 100 : ℝ) (1138829 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (13 / 100 : ℝ))) h 2
    have he :
        (Real.exp (13 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (13 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1293691 / 1000000 : ℝ) - (13 / 100 : ℝ) / 2) / 32)
      (56652447 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_104 :
    ∀ u : ℝ, (13 / 100 : ℝ) ≤ u → u ≤ (21 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (38907397 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (13 / 100 : ℝ) (21 / 160 : ℝ) (129693 / 100000 : ℝ) (1300176904009 / 1000000000000 : ℝ)
    (113338697 / 100000000 : ℝ) (90963489 / 5000000000 : ℝ) (38907397 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (13 / 100 : ℝ)) (129693 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (21 / 160 : ℝ) (1140253 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (21 / 160 : ℝ))) h 2
    have he :
        (Real.exp (21 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (21 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (129693 / 100000 : ℝ) - (21 / 160 : ℝ) / 2) / 32)
      (113338697 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_105 :
    ∀ u : ℝ, (21 / 160 : ℝ) ≤ u → u ≤ (53 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (155142609 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (21 / 160 : ℝ) (53 / 400 : ℝ) (81261 / 62500 : ℝ) (203661441 / 156250000 : ℝ)
    (113372589 / 100000000 : ℝ) (18019467 / 1000000000 : ℝ) (155142609 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (21 / 160 : ℝ)) (81261 / 62500 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (53 / 400 : ℝ) (14271 / 12500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (53 / 400 : ℝ))) h 2
    have he :
        (Real.exp (53 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (53 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (81261 / 62500 : ℝ) - (53 / 400 : ℝ) / 2) / 32)
      (113372589 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_106 :
    ∀ u : ℝ, (53 / 400 : ℝ) ≤ u → u ≤ (107 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (9665737 / 6250000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (53 / 400 : ℝ) (107 / 800 : ℝ) (130343 / 100000 : ℝ) (81668493729 / 62500000000 : ℝ)
    (113406579 / 100000000 : ℝ) (2788663 / 156250000 : ℝ) (9665737 / 6250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (53 / 400 : ℝ)) (130343 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (107 / 800 : ℝ) (285777 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (107 / 800 : ℝ))) h 2
    have he :
        (Real.exp (107 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (107 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (130343 / 100000 : ℝ) - (107 / 800 : ℝ) / 2) / 32)
      (113406579 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_107 :
    ∀ u : ℝ, (107 / 800 : ℝ) ≤ u → u ≤ (27 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (30831313 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (107 / 800 : ℝ) (27 / 200 : ℝ) (1306693 / 1000000 : ℝ) (1309964944369 / 1000000000000 : ℝ)
    (2836017 / 2500000 : ℝ) (176765589 / 10000000000 : ℝ) (30831313 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (107 / 800 : ℝ)) (1306693 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (27 / 200 : ℝ) (1144537 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (27 / 200 : ℝ))) h 2
    have he :
        (Real.exp (27 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (27 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1306693 / 1000000 : ℝ) - (27 / 200 : ℝ) / 2) / 32)
      (2836017 / 2500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_108 :
    ∀ u : ℝ, (27 / 200 : ℝ) ≤ u → u ≤ (109 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (153659257 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (27 / 200 : ℝ) (109 / 800 : ℝ) (327491 / 250000 : ℝ) (1313244948961 / 1000000000000 : ℝ)
    (354609 / 312500 : ℝ) (87534363 / 5000000000 : ℝ) (153659257 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (27 / 200 : ℝ)) (327491 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (109 / 800 : ℝ) (1145969 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (109 / 800 : ℝ))) h 2
    have he :
        (Real.exp (109 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (109 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (327491 / 250000 : ℝ) - (109 / 800 : ℝ) / 2) / 32)
      (354609 / 312500 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_109 :
    ∀ u : ℝ, (109 / 800 : ℝ) ≤ u → u ≤ (11 / 80 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (15315819 / 10000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (109 / 800 : ℝ) (11 / 80 : ℝ) (1313243 / 1000000 : ℝ) (329132837401 / 250000000000 : ℝ)
    (5675459 / 5000000 : ℝ) (173383769 / 10000000000 : ℝ) (15315819 / 10000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (109 / 800 : ℝ)) (1313243 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (11 / 80 : ℝ) (573701 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (11 / 80 : ℝ))) h 2
    have he :
        (Real.exp (11 / 80 : ℝ)) ^ 2 =
          Real.exp (2 * (11 / 80 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1313243 / 1000000 : ℝ) - (11 / 80 : ℝ) / 2) / 32)
      (5675459 / 5000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_110 :
    ∀ u : ℝ, (11 / 80 : ℝ) ≤ u → u ≤ (111 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (38163573 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (11 / 80 : ℝ) (111 / 800 : ℝ) (131653 / 100000 : ℝ) (1319826452569 / 1000000000000 : ℝ)
    (113543579 / 100000000 : ℝ) (171710739 / 10000000000 : ℝ) (38163573 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (11 / 80 : ℝ)) (131653 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (111 / 800 : ℝ) (1148837 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (111 / 800 : ℝ))) h 2
    have he :
        (Real.exp (111 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (111 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (131653 / 100000 : ℝ) - (111 / 800 : ℝ) / 2) / 32)
      (113543579 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_111 :
    ∀ u : ℝ, (111 / 800 : ℝ) ≤ u → u ≤ (7 / 50 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (15214703 / 10000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (111 / 800 : ℝ) (7 / 50 : ℝ) (659913 / 500000 : ℝ) (330782568769 / 250000000000 : ℝ)
    (113578089 / 100000000 : ℝ) (85024517 / 5000000000 : ℝ) (15214703 / 10000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (111 / 800 : ℝ)) (659913 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (7 / 50 : ℝ) (575137 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (7 / 50 : ℝ))) h 2
    have he :
        (Real.exp (7 / 50 : ℝ)) ^ 2 =
          Real.exp (2 * (7 / 50 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (659913 / 500000 : ℝ) - (7 / 50 : ℝ) / 2) / 32)
      (113578089 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_112 :
    ∀ u : ℝ, (7 / 50 : ℝ) ≤ u → u ≤ (113 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2369337 / 1562500 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (7 / 50 : ℝ) (113 / 800 : ℝ) (1323129 / 1000000 : ℝ) (1326442834369 / 1000000000000 : ℝ)
    (113612687 / 100000000 : ℝ) (84199867 / 5000000000 : ℝ) (2369337 / 1562500 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (7 / 50 : ℝ)) (1323129 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (113 / 800 : ℝ) (1151713 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (113 / 800 : ℝ))) h 2
    have he :
        (Real.exp (113 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (113 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1323129 / 1000000 : ℝ) - (113 / 800 : ℝ) / 2) / 32)
      (113612687 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_113 :
    ∀ u : ℝ, (113 / 800 : ℝ) ≤ u → u ≤ (57 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (75562397 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (113 / 800 : ℝ) (57 / 400 : ℝ) (1326441 / 1000000 : ℝ) (332441036929 / 250000000000 : ℝ)
    (113647397 / 100000000 : ℝ) (83380833 / 5000000000 : ℝ) (75562397 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (113 / 800 : ℝ)) (1326441 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (57 / 400 : ℝ) (576577 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (57 / 400 : ℝ))) h 2
    have he :
        (Real.exp (57 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (57 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1326441 / 1000000 : ℝ) - (57 / 400 : ℝ) / 2) / 32)
      (113647397 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_114 :
    ∀ u : ℝ, (57 / 400 : ℝ) ≤ u → u ≤ (23 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (37652009 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (57 / 400 : ℝ) (23 / 160 : ℝ) (664881 / 500000 : ℝ) (83318245201 / 62500000000 : ℝ)
    (113682217 / 100000000 : ℝ) (165134911 / 10000000000 : ℝ) (37652009 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (57 / 400 : ℝ)) (664881 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (23 / 160 : ℝ) (288649 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (23 / 160 : ℝ))) h 2
    have he :
        (Real.exp (23 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (23 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (664881 / 500000 : ℝ) - (23 / 160 : ℝ) / 2) / 32)
      (113682217 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_115 :
    ∀ u : ℝ, (23 / 160 : ℝ) ≤ u → u ≤ (29 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (18761147 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (23 / 160 : ℝ) (29 / 200 : ℝ) (133309 / 100000 : ℝ) (835267801 / 625000000 : ℝ)
    (56858563 / 50000000 : ℝ) (163520421 / 10000000000 : ℝ) (18761147 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (23 / 160 : ℝ)) (133309 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (29 / 200 : ℝ) (28901 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (29 / 200 : ℝ))) h 2
    have he :
        (Real.exp (29 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (29 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (133309 / 100000 : ℝ) - (29 / 200 : ℝ) / 2) / 32)
      (56858563 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_116 :
    ∀ u : ℝ, (29 / 200 : ℝ) ≤ u → u ≤ (117 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (37391801 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (29 / 200 : ℝ) (117 / 800 : ℝ) (1336427 / 1000000 : ℝ) (334943460049 / 250000000000 : ℝ)
    (56876073 / 50000000 : ℝ) (40479287 / 2500000000 : ℝ) (37391801 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (29 / 200 : ℝ)) (1336427 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (117 / 800 : ℝ) (578743 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (117 / 800 : ℝ))) h 2
    have he :
        (Real.exp (117 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (117 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1336427 / 1000000 : ℝ) - (117 / 800 : ℝ) / 2) / 32)
      (56876073 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_117 :
    ∀ u : ℝ, (117 / 800 : ℝ) ≤ u → u ≤ (59 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (29808539 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (117 / 800 : ℝ) (59 / 400 : ℝ) (334943 / 250000 : ℝ) (335782004089 / 250000000000 : ℝ)
    (56893633 / 50000000 : ℝ) (40081393 / 2500000000 : ℝ) (29808539 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (117 / 800 : ℝ)) (334943 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (59 / 400 : ℝ) (579467 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (59 / 400 : ℝ))) h 2
    have he :
        (Real.exp (59 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (59 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (334943 / 250000 : ℝ) - (59 / 400 : ℝ) / 2) / 32)
      (56893633 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_118 :
    ∀ u : ℝ, (59 / 400 : ℝ) ≤ u → u ≤ (119 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (7425717 / 5000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (59 / 400 : ℝ) (119 / 800 : ℝ) (671563 / 500000 : ℝ) (1346488706689 / 1000000000000 : ℝ)
    (56911249 / 50000000 : ℝ) (1269961 / 80000000 : ℝ) (7425717 / 5000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (59 / 400 : ℝ)) (671563 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (119 / 800 : ℝ) (1160383 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (119 / 800 : ℝ))) h 2
    have he :
        (Real.exp (119 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (119 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (671563 / 500000 : ℝ) - (119 / 800 : ℝ) / 2) / 32)
      (56911249 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_119 :
    ∀ u : ℝ, (119 / 800 : ℝ) ≤ u → u ≤ (3 / 20 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (147984337 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (119 / 800 : ℝ) (3 / 20 : ℝ) (168311 / 125000 : ℝ) (53994422689 / 40000000000 : ℝ)
    (11385783 / 10000000 : ℝ) (157176323 / 10000000000 : ℝ) (147984337 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (119 / 800 : ℝ)) (168311 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (3 / 20 : ℝ) (232367 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (3 / 20 : ℝ))) h 2
    have he :
        (Real.exp (3 / 20 : ℝ)) ^ 2 =
          Real.exp (2 * (3 / 20 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (168311 / 125000 : ℝ) - (3 / 20 : ℝ) / 2) / 32)
      (11385783 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_100
#print axioms hpThetaEnergyUpper_interval_119

end HodgeProofHP
