import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_280 :
    ∀ u : ℝ, (7 / 20 : ℝ) ≤ u → u ≤ (281 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (53101779 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (7 / 20 : ℝ) (281 / 800 : ℝ) (251719 / 125000 : ℝ) (2018794830649 / 1000000000000 : ℝ)
    (60590259 / 50000000 : ℝ) (21387019 / 10000000000 : ℝ) (53101779 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (7 / 20 : ℝ)) (251719 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (281 / 800 : ℝ) (1420843 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (281 / 800 : ℝ))) h 2
    have he :
        (Real.exp (281 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (281 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (251719 / 125000 : ℝ) - (281 / 800 : ℝ) / 2) / 32)
      (60590259 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_281 :
    ∀ u : ℝ, (281 / 800 : ℝ) ≤ u → u ≤ (141 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (10520577 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (281 / 800 : ℝ) (141 / 400 : ℝ) (2018793 / 1000000 : ℝ) (5059619161 / 2500000000 : ℝ)
    (60619053 / 50000000 : ℝ) (21064319 / 10000000000 : ℝ) (10520577 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (281 / 800 : ℝ)) (2018793 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (141 / 400 : ℝ) (71131 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (141 / 400 : ℝ))) h 2
    have he :
        (Real.exp (141 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (141 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2018793 / 1000000 : ℝ) - (141 / 400 : ℝ) / 2) / 32)
      (60619053 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_282 :
    ∀ u : ℝ, (141 / 400 : ℝ) ≤ u → u ≤ (283 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (52106727 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (141 / 400 : ℝ) (283 / 800 : ℝ) (1011923 / 500000 : ℝ) (12680721 / 6250000 : ℝ)
    (24259173 / 20000000 : ℝ) (10372851 / 5000000000 : ℝ) (52106727 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (141 / 400 : ℝ)) (1011923 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (283 / 800 : ℝ) (3561 / 2500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (283 / 800 : ℝ))) h 2
    have he :
        (Real.exp (283 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (283 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1011923 / 500000 : ℝ) - (283 / 800 : ℝ) / 2) / 32)
      (24259173 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_283 :
    ∀ u : ℝ, (283 / 800 : ℝ) ≤ u → u ≤ (71 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (3225799 / 6250000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (283 / 800 : ℝ) (71 / 200 : ℝ) (126807 / 62500 : ℝ) (2033992244761 / 1000000000000 : ℝ)
    (60676903 / 50000000 : ℝ) (638471 / 312500000 : ℝ) (3225799 / 6250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (283 / 800 : ℝ)) (126807 / 62500 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (71 / 200 : ℝ) (1426181 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (71 / 200 : ℝ))) h 2
    have he :
        (Real.exp (71 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (71 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (126807 / 62500 : ℝ) - (71 / 200 : ℝ) / 2) / 32)
      (60676903 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_284 :
    ∀ u : ℝ, (71 / 200 : ℝ) ≤ u → u ≤ (57 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (25560723 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (71 / 200 : ℝ) (57 / 160 : ℝ) (2033991 / 1000000 : ℝ) (81563361649 / 40000000000 : ℝ)
    (12141193 / 10000000 : ℝ) (2012039 / 1000000000 : ℝ) (25560723 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (71 / 200 : ℝ)) (2033991 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (57 / 160 : ℝ) (285593 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (57 / 160 : ℝ))) h 2
    have he :
        (Real.exp (57 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (57 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2033991 / 1000000 : ℝ) - (57 / 160 : ℝ) / 2) / 32)
      (12141193 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_285 :
    ∀ u : ℝ, (57 / 160 : ℝ) ≤ u → u ≤ (143 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (50632729 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (57 / 160 : ℝ) (143 / 400 : ℝ) (1019541 / 500000 : ℝ) (2044187922001 / 1000000000000 : ℝ)
    (7591889 / 6250000 : ℝ) (19813691 / 10000000000 : ℝ) (50632729 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (57 / 160 : ℝ)) (1019541 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (143 / 400 : ℝ) (1429751 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (143 / 400 : ℝ))) h 2
    have he :
        (Real.exp (143 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (143 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1019541 / 500000 : ℝ) - (143 / 400 : ℝ) / 2) / 32)
      (7591889 / 6250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_286 :
    ∀ u : ℝ, (143 / 400 : ℝ) ≤ u → u ≤ (287 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (12536613 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (143 / 400 : ℝ) (287 / 800 : ℝ) (1022093 / 500000 : ℝ) (2049303908521 / 1000000000000 : ℝ)
    (60764351 / 50000000 : ℝ) (1219429 / 625000000 : ℝ) (12536613 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (143 / 400 : ℝ)) (1022093 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (287 / 800 : ℝ) (1431539 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (287 / 800 : ℝ))) h 2
    have he :
        (Real.exp (287 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (287 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1022093 / 500000 : ℝ) - (287 / 800 : ℝ) / 2) / 32)
      (60764351 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_287 :
    ∀ u : ℝ, (287 / 800 : ℝ) ≤ u → u ≤ (9 / 25 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (49662841 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (287 / 800 : ℝ) (9 / 25 : ℝ) (2049303 / 1000000 : ℝ) (20544348889 / 10000000000 : ℝ)
    (121587363 / 100000000 : ℝ) (4802971 / 2500000000 : ℝ) (49662841 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (287 / 800 : ℝ)) (2049303 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (9 / 25 : ℝ) (143333 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (9 / 25 : ℝ))) h 2
    have he :
        (Real.exp (9 / 25 : ℝ)) ^ 2 =
          Real.exp (2 * (9 / 25 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2049303 / 1000000 : ℝ) - (9 / 25 : ℝ) / 2) / 32)
      (121587363 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_288 :
    ∀ u : ℝ, (9 / 25 : ℝ) ≤ u → u ≤ (289 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (24590863 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (9 / 25 : ℝ) (289 / 800 : ℝ) (2054433 / 1000000 : ℝ) (2059578025129 / 1000000000000 : ℝ)
    (121646207 / 100000000 : ℝ) (3783343 / 2000000000 : ℝ) (24590863 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (9 / 25 : ℝ)) (2054433 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (289 / 800 : ℝ) (1435123 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (289 / 800 : ℝ))) h 2
    have he :
        (Real.exp (289 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (289 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2054433 / 1000000 : ℝ) - (289 / 800 : ℝ) / 2) / 32)
      (121646207 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_289 :
    ∀ u : ℝ, (289 / 800 : ℝ) ≤ u → u ≤ (29 / 80 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (48703279 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (289 / 800 : ℝ) (29 / 80 : ℝ) (82383 / 40000 : ℝ) (516183334681 / 250000000000 : ℝ)
    (121705223 / 100000000 : ℝ) (9312689 / 5000000000 : ℝ) (48703279 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (289 / 800 : ℝ)) (82383 / 40000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (29 / 80 : ℝ) (718459 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (29 / 80 : ℝ))) h 2
    have he :
        (Real.exp (29 / 80 : ℝ)) ^ 2 =
          Real.exp (2 * (29 / 80 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (82383 / 40000 : ℝ) - (29 / 80 : ℝ) / 2) / 32)
      (121705223 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_290 :
    ∀ u : ℝ, (29 / 80 : ℝ) ≤ u → u ≤ (291 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (24113599 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (29 / 80 : ℝ) (291 / 800 : ℝ) (2064731 / 1000000 : ℝ) (82796034049 / 40000000000 : ℝ)
    (24352887 / 20000000 : ℝ) (18337721 / 10000000000 : ℝ) (24113599 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (29 / 80 : ℝ)) (2064731 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (291 / 800 : ℝ) (287743 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (291 / 800 : ℝ))) h 2
    have he :
        (Real.exp (291 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (291 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2064731 / 1000000 : ℝ) - (291 / 800 : ℝ) / 2) / 32)
      (24352887 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_291 :
    ∀ u : ℝ, (291 / 800 : ℝ) ≤ u → u ≤ (73 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (11938499 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (291 / 800 : ℝ) (73 / 200 : ℝ) (2069899 / 1000000 : ℝ) (83003338609 / 40000000000 : ℝ)
    (121823819 / 100000000 : ℝ) (4513457 / 2500000000 : ℝ) (11938499 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (291 / 800 : ℝ)) (2069899 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (73 / 200 : ℝ) (288103 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (73 / 200 : ℝ))) h 2
    have he :
        (Real.exp (73 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (73 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2069899 / 1000000 : ℝ) - (73 / 200 : ℝ) / 2) / 32)
      (121823819 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_292 :
    ∀ u : ℝ, (73 / 200 : ℝ) ≤ u → u ≤ (293 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (23641587 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (73 / 200 : ℝ) (293 / 800 : ℝ) (51877 / 25000 : ℝ) (130017215241 / 62500000000 : ℝ)
    (30470847 / 25000000 : ℝ) (8886801 / 5000000000 : ℝ) (23641587 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (73 / 200 : ℝ)) (51877 / 25000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (293 / 800 : ℝ) (360579 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (293 / 800 : ℝ))) h 2
    have he :
        (Real.exp (293 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (293 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (51877 / 25000 : ℝ) - (293 / 800 : ℝ) / 2) / 32)
      (30470847 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_293 :
    ∀ u : ℝ, (293 / 800 : ℝ) ≤ u → u ≤ (147 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (365743 / 781250 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (293 / 800 : ℝ) (147 / 400 : ℝ) (1040137 / 500000 : ℝ) (1303426609 / 625000000 : ℝ)
    (121943141 / 100000000 : ℝ) (8748507 / 5000000000 : ℝ) (365743 / 781250 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (293 / 800 : ℝ)) (1040137 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (147 / 400 : ℝ) (36103 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (147 / 400 : ℝ))) h 2
    have he :
        (Real.exp (147 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (147 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1040137 / 500000 : ℝ) - (147 / 400 : ℝ) / 2) / 32)
      (121943141 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_294 :
    ∀ u : ℝ, (147 / 400 : ℝ) ≤ u → u ≤ (59 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1853991 / 4000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (147 / 400 : ℝ) (59 / 160 : ℝ) (2085481 / 1000000 : ℝ) (2090704889329 / 1000000000000 : ℝ)
    (3050077 / 2500000 : ℝ) (8612011 / 5000000000 : ℝ) (1853991 / 4000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (147 / 400 : ℝ)) (2085481 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (59 / 160 : ℝ) (1445927 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (59 / 160 : ℝ))) h 2
    have he :
        (Real.exp (59 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (59 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2085481 / 1000000 : ℝ) - (59 / 160 : ℝ) / 2) / 32)
      (3050077 / 2500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_295 :
    ∀ u : ℝ, (59 / 160 : ℝ) ≤ u → u ≤ (37 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (45886749 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (59 / 160 : ℝ) (37 / 100 : ℝ) (1045351 / 500000 : ℝ) (83837465209 / 40000000000 : ℝ)
    (24412643 / 20000000 : ℝ) (339091 / 200000000 : ℝ) (45886749 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (59 / 160 : ℝ)) (1045351 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (37 / 100 : ℝ) (289547 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (37 / 100 : ℝ))) h 2
    have he :
        (Real.exp (37 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (37 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1045351 / 500000 : ℝ) - (37 / 100 : ℝ) / 2) / 32)
      (24412643 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_296 :
    ∀ u : ℝ, (37 / 100 : ℝ) ≤ u → u ≤ (297 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (5678331 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (37 / 100 : ℝ) (297 / 800 : ℝ) (419187 / 200000 : ℝ) (525295901529 / 250000000000 : ℝ)
    (30530881 / 25000000 : ℝ) (8344331 / 5000000000 : ℝ) (5678331 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (37 / 100 : ℝ)) (419187 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (297 / 800 : ℝ) (724773 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (297 / 800 : ℝ))) h 2
    have he :
        (Real.exp (297 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (297 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (419187 / 200000 : ℝ) - (297 / 800 : ℝ) / 2) / 32)
      (30530881 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_297 :
    ∀ u : ℝ, (297 / 800 : ℝ) ≤ u → u ≤ (149 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (8993837 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (297 / 800 : ℝ) (149 / 400 : ℝ) (2101181 / 1000000 : ℝ) (2106442946881 / 1000000000000 : ℝ)
    (61092009 / 50000000 : ℝ) (4106569 / 2500000000 : ℝ) (8993837 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (297 / 800 : ℝ)) (2101181 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (149 / 400 : ℝ) (1451359 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (149 / 400 : ℝ))) h 2
    have he :
        (Real.exp (149 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (149 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2101181 / 1000000 : ℝ) - (149 / 400 : ℝ) / 2) / 32)
      (61092009 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_298 :
    ∀ u : ℝ, (149 / 400 : ℝ) ≤ u → u ≤ (299 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (4451421 / 10000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (149 / 400 : ℝ) (299 / 800 : ℝ) (2106441 / 1000000 : ℝ) (527928668569 / 250000000000 : ℝ)
    (122244711 / 100000000 : ℝ) (16167301 / 10000000000 : ℝ) (4451421 / 10000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (149 / 400 : ℝ)) (2106441 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (299 / 800 : ℝ) (726587 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (299 / 800 : ℝ))) h 2
    have he :
        (Real.exp (299 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (299 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2106441 / 1000000 : ℝ) - (299 / 800 : ℝ) / 2) / 32)
      (122244711 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_299 :
    ∀ u : ℝ, (299 / 800 : ℝ) ≤ u → u ≤ (3 / 8 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (44062061 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (299 / 800 : ℝ) (3 / 8 : ℝ) (1055857 / 500000 : ℝ) (8269537969 / 3906250000 : ℝ)
    (122305589 / 100000000 : ℝ) (15911763 / 10000000000 : ℝ) (44062061 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (299 / 800 : ℝ)) (1055857 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (3 / 8 : ℝ) (90937 / 62500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (3 / 8 : ℝ))) h 2
    have he :
        (Real.exp (3 / 8 : ℝ)) ^ 2 =
          Real.exp (2 * (3 / 8 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1055857 / 500000 : ℝ) - (3 / 8 : ℝ) / 2) / 32)
      (122305589 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_280
#print axioms hpThetaEnergyUpper_interval_299

end HodgeProofHP
