import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_140 :
    ∀ u : ℝ, (7 / 40 : ℝ) ≤ u → u ≤ (141 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (68131859 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (7 / 40 : ℝ) (141 / 800 : ℝ) (1419067 / 1000000 : ℝ) (1422621551169 / 1000000000000 : ℝ)
    (4584983 / 4000000 : ℝ) (126797991 / 10000000000 : ℝ) (68131859 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (7 / 40 : ℝ)) (1419067 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (141 / 800 : ℝ) (1192737 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (141 / 800 : ℝ))) h 2
    have he :
        (Real.exp (141 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (141 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1419067 / 1000000 : ℝ) - (141 / 800 : ℝ) / 2) / 32)
      (4584983 / 4000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_141 :
    ∀ u : ℝ, (141 / 800 : ℝ) ≤ u → u ≤ (71 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (135681383 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (141 / 800 : ℝ) (71 / 400 : ℝ) (1422619 / 1000000 : ℝ) (1426182904441 / 1000000000000 : ℝ)
    (57331147 / 50000000 : ℝ) (62735009 / 5000000000 : ℝ) (135681383 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (141 / 800 : ℝ)) (1422619 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (71 / 400 : ℝ) (1194229 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (71 / 400 : ℝ))) h 2
    have he :
        (Real.exp (71 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (71 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1422619 / 1000000 : ℝ) - (71 / 400 : ℝ) / 2) / 32)
      (57331147 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_142 :
    ∀ u : ℝ, (71 / 400 : ℝ) ≤ u → u ≤ (143 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (5403861 / 4000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (71 / 400 : ℝ) (143 / 800 : ℝ) (71309 / 50000 : ℝ) (357437775321 / 250000000000 : ℝ)
    (57350063 / 50000000 : ℝ) (124152469 / 10000000000 : ℝ) (5403861 / 4000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (71 / 400 : ℝ)) (71309 / 50000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (143 / 800 : ℝ) (597861 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (143 / 800 : ℝ))) h 2
    have he :
        (Real.exp (143 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (143 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (71309 / 50000 : ℝ) - (143 / 800 : ℝ) / 2) / 32)
      (57350063 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_143 :
    ∀ u : ℝ, (143 / 800 : ℝ) ≤ u → u ≤ (9 / 50 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (134510479 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (143 / 800 : ℝ) (9 / 50 : ℝ) (5719 / 4000 : ℝ) (358332734881 / 250000000000 : ℝ)
    (114738073 / 100000000 : ℝ) (30711311 / 2500000000 : ℝ) (134510479 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (143 / 800 : ℝ)) (5719 / 4000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (9 / 50 : ℝ) (598609 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (9 / 50 : ℝ))) h 2
    have he :
        (Real.exp (9 / 50 : ℝ)) ^ 2 =
          Real.exp (2 * (9 / 50 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (5719 / 4000 : ℝ) - (9 / 50 : ℝ) / 2) / 32)
      (114738073 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_144 :
    ∀ u : ℝ, (9 / 50 : ℝ) ≤ u → u ≤ (29 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (133922023 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (9 / 50 : ℝ) (29 / 160 : ℝ) (1433329 / 1000000 : ℝ) (57476706049 / 40000000000 : ℝ)
    (114776133 / 100000000 : ℝ) (60774189 / 5000000000 : ℝ) (133922023 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (9 / 50 : ℝ)) (1433329 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (29 / 160 : ℝ) (239743 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (29 / 160 : ℝ))) h 2
    have he :
        (Real.exp (29 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (29 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1433329 / 1000000 : ℝ) - (29 / 160 : ℝ) / 2) / 32)
      (114776133 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_145 :
    ∀ u : ℝ, (29 / 160 : ℝ) ≤ u → u ≤ (73 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (133332509 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (29 / 160 : ℝ) (73 / 400 : ℝ) (1436917 / 1000000 : ℝ) (57620641849 / 40000000000 : ℝ)
    (114814307 / 100000000 : ℝ) (24052361 / 2000000000 : ℝ) (133332509 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (29 / 160 : ℝ)) (1436917 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (73 / 400 : ℝ) (240043 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (73 / 400 : ℝ))) h 2
    have he :
        (Real.exp (73 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (73 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1436917 / 1000000 : ℝ) - (73 / 400 : ℝ) / 2) / 32)
      (114814307 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_146 :
    ∀ u : ℝ, (73 / 400 : ℝ) ≤ u → u ≤ (147 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (132740659 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (73 / 400 : ℝ) (147 / 800 : ℝ) (720257 / 500000 : ℝ) (90257584041 / 62500000000 : ℝ)
    (22970519 / 20000000 : ℝ) (29746373 / 2500000000 : ℝ) (132740659 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (73 / 400 : ℝ)) (720257 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (147 / 800 : ℝ) (300429 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (147 / 800 : ℝ))) h 2
    have he :
        (Real.exp (147 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (147 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (720257 / 500000 : ℝ) - (147 / 800 : ℝ) / 2) / 32)
      (22970519 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_147 :
    ∀ u : ℝ, (147 / 800 : ℝ) ≤ u → u ≤ (37 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (66073821 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (147 / 800 : ℝ) (37 / 200 : ℝ) (1444119 / 1000000 : ℝ) (1447735961961 / 1000000000000 : ℝ)
    (57445493 / 50000000 : ℝ) (58859883 / 5000000000 : ℝ) (66073821 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (147 / 800 : ℝ)) (1444119 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (37 / 200 : ℝ) (1203219 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (37 / 200 : ℝ))) h 2
    have he :
        (Real.exp (37 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (37 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1444119 / 1000000 : ℝ) - (37 / 200 : ℝ) / 2) / 32)
      (57445493 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_148 :
    ∀ u : ℝ, (37 / 200 : ℝ) ≤ u → u ≤ (149 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (131552571 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (37 / 200 : ℝ) (149 / 800 : ℝ) (723867 / 500000 : ℝ) (90709994761 / 62500000000 : ℝ)
    (114929503 / 100000000 : ℝ) (23292767 / 2000000000 : ℝ) (131552571 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (37 / 200 : ℝ)) (723867 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (149 / 800 : ℝ) (301181 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (149 / 800 : ℝ))) h 2
    have he :
        (Real.exp (149 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (149 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (723867 / 500000 : ℝ) - (149 / 800 : ℝ) / 2) / 32)
      (114929503 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_149 :
    ∀ u : ℝ, (149 / 800 : ℝ) ≤ u → u ≤ (3 / 16 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (65477991 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (149 / 800 : ℝ) (3 / 16 : ℝ) (725679 / 500000 : ℝ) (1454993225361 / 1000000000000 : ℝ)
    (57484067 / 50000000 : ℝ) (5760903 / 500000000 : ℝ) (65477991 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (149 / 800 : ℝ)) (725679 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (3 / 16 : ℝ) (1206231 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (3 / 16 : ℝ))) h 2
    have he :
        (Real.exp (3 / 16 : ℝ)) ^ 2 =
          Real.exp (2 * (3 / 16 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (725679 / 500000 : ℝ) - (3 / 16 : ℝ) / 2) / 32)
      (57484067 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_150 :
    ∀ u : ℝ, (3 / 16 : ℝ) ≤ u → u ≤ (151 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (65178627 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (3 / 16 : ℝ) (151 / 800 : ℝ) (1454991 / 1000000 : ℝ) (1458633492121 / 1000000000000 : ℝ)
    (718793 / 625000 : ℝ) (14247797 / 1250000000 : ℝ) (65178627 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (3 / 16 : ℝ)) (1454991 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (151 / 800 : ℝ) (1207739 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (151 / 800 : ℝ))) h 2
    have he :
        (Real.exp (151 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (151 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1454991 / 1000000 : ℝ) - (151 / 800 : ℝ) / 2) / 32)
      (718793 / 625000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_151 :
    ∀ u : ℝ, (151 / 800 : ℝ) ≤ u → u ≤ (19 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (129757719 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (151 / 800 : ℝ) (19 / 100 : ℝ) (1458633 / 1000000 : ℝ) (23396569 / 16000000 : ℝ)
    (115045741 / 100000000 : ℝ) (112756747 / 10000000000 : ℝ) (129757719 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (151 / 800 : ℝ)) (1458633 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (19 / 100 : ℝ) (4837 / 4000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (19 / 100 : ℝ))) h 2
    have he :
        (Real.exp (19 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (19 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1458633 / 1000000 : ℝ) - (19 / 100 : ℝ) / 2) / 32)
      (115045741 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_152 :
    ∀ u : ℝ, (19 / 100 : ℝ) ≤ u → u ≤ (153 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (64578411 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (19 / 100 : ℝ) (153 / 800 : ℝ) (365571 / 250000 : ℝ) (1465947042169 / 1000000000000 : ℝ)
    (28771179 / 25000000 : ℝ) (111541169 / 10000000000 : ℝ) (64578411 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (19 / 100 : ℝ)) (365571 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (153 / 800 : ℝ) (1210763 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (153 / 800 : ℝ))) h 2
    have he :
        (Real.exp (153 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (153 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (365571 / 250000 : ℝ) - (153 / 800 : ℝ) / 2) / 32)
      (28771179 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_153 :
    ∀ u : ℝ, (153 / 800 : ℝ) ≤ u → u ≤ (77 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (32138487 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (153 / 800 : ℝ) (77 / 400 : ℝ) (183243 / 125000 : ℝ) (1469615524729 / 1000000000000 : ℝ)
    (57561903 / 50000000 : ℝ) (110335573 / 10000000000 : ℝ) (32138487 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (153 / 800 : ℝ)) (183243 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (77 / 400 : ℝ) (1212277 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (77 / 400 : ℝ))) h 2
    have he :
        (Real.exp (77 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (77 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (183243 / 125000 : ℝ) - (77 / 400 : ℝ) / 2) / 32)
      (57561903 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_154 :
    ∀ u : ℝ, (77 / 400 : ℝ) ≤ u → u ≤ (31 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (63974659 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (77 / 400 : ℝ) (31 / 160 : ℝ) (734807 / 500000 : ℝ) (1473293446849 / 1000000000000 : ℝ)
    (115163023 / 100000000 : ℝ) (109139559 / 10000000000 : ℝ) (63974659 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (77 / 400 : ℝ)) (734807 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (31 / 160 : ℝ) (1213793 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (31 / 160 : ℝ))) h 2
    have he :
        (Real.exp (31 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (31 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (734807 / 500000 : ℝ) - (31 / 160 : ℝ) / 2) / 32)
      (115163023 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_155 :
    ∀ u : ℝ, (31 / 160 : ℝ) ≤ u → u ≤ (39 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (127343919 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (31 / 160 : ℝ) (39 / 200 : ℝ) (368323 / 250000 : ℝ) (1476980826721 / 1000000000000 : ℝ)
    (115202343 / 100000000 : ℝ) (53976911 / 5000000000 : ℝ) (127343919 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (31 / 160 : ℝ)) (368323 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (39 / 200 : ℝ) (1215311 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (39 / 200 : ℝ))) h 2
    have he :
        (Real.exp (39 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (39 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (368323 / 250000 : ℝ) - (39 / 200 : ℝ) / 2) / 32)
      (115202343 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_156 :
    ∀ u : ℝ, (39 / 200 : ℝ) ≤ u → u ≤ (157 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (126737513 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (39 / 200 : ℝ) (157 / 800 : ℝ) (73849 / 50000 : ℝ) (361494169 / 244140625 : ℝ)
    (115241789 / 100000000 : ℝ) (26694407 / 2500000000 : ℝ) (126737513 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (39 / 200 : ℝ)) (73849 / 50000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (157 / 800 : ℝ) (19013 / 15625 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (157 / 800 : ℝ))) h 2
    have he :
        (Real.exp (157 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (157 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (73849 / 50000 : ℝ) - (157 / 800 : ℝ) / 2) / 32)
      (115241789 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_157 :
    ∀ u : ℝ, (157 / 800 : ℝ) ≤ u → u ≤ (79 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (63064661 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (157 / 800 : ℝ) (79 / 400 : ℝ) (1480677 / 1000000 : ℝ) (371096617329 / 250000000000 : ℝ)
    (115281351 / 100000000 : ℝ) (52805623 / 5000000000 : ℝ) (63064661 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (157 / 800 : ℝ)) (1480677 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (79 / 400 : ℝ) (609177 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (79 / 400 : ℝ))) h 2
    have he :
        (Real.exp (79 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (79 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1480677 / 1000000 : ℝ) - (79 / 400 : ℝ) / 2) / 32)
      (115281351 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_158 :
    ∀ u : ℝ, (79 / 400 : ℝ) ≤ u → u ≤ (159 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (125518983 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (79 / 400 : ℝ) (159 / 800 : ℝ) (46387 / 31250 : ℝ) (1488099895129 / 1000000000000 : ℝ)
    (1441513 / 1250000 : ℝ) (26113579 / 2500000000 : ℝ) (125518983 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (79 / 400 : ℝ)) (46387 / 31250 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (159 / 800 : ℝ) (1219877 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (159 / 800 : ℝ))) h 2
    have he :
        (Real.exp (159 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (159 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (46387 / 31250 : ℝ) - (159 / 800 : ℝ) / 2) / 32)
      (1441513 / 1250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_159 :
    ∀ u : ℝ, (159 / 800 : ℝ) ≤ u → u ≤ (1 / 5 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (62454321 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (159 / 800 : ℝ) (1 / 5 : ℝ) (1488099 / 1000000 : ℝ) (1491825288409 / 1000000000000 : ℝ)
    (115360833 / 100000000 : ℝ) (6456717 / 625000000 : ℝ) (62454321 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (159 / 800 : ℝ)) (1488099 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (1 / 5 : ℝ) (1221403 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (1 / 5 : ℝ))) h 2
    have he :
        (Real.exp (1 / 5 : ℝ)) ^ 2 =
          Real.exp (2 * (1 / 5 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1488099 / 1000000 : ℝ) - (1 / 5 : ℝ) / 2) / 32)
      (115360833 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_140
#print axioms hpThetaEnergyUpper_interval_159

end HodgeProofHP
