import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_240 :
    ∀ u : ℝ, (3 / 10 : ℝ) ≤ u → u ≤ (241 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (74902469 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (3 / 10 : ℝ) (241 / 800 : ℝ) (911059 / 500000 : ℝ) (114167624769 / 62500000000 : ℝ)
    (929813 / 781250 : ℝ) (38073371 / 10000000000 : ℝ) (74902469 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (3 / 10 : ℝ)) (911059 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (241 / 800 : ℝ) (337887 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (241 / 800 : ℝ))) h 2
    have he :
        (Real.exp (241 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (241 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (911059 / 500000 : ℝ) - (241 / 800 : ℝ) / 2) / 32)
      (929813 / 781250 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_241 :
    ∀ u : ℝ, (241 / 800 : ℝ) ≤ u → u ≤ (121 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2322457 / 3125000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (241 / 800 : ℝ) (121 / 400 : ℝ) (1826679 / 1000000 : ℝ) (457813271161 / 250000000000 : ℝ)
    (14883377 / 12500000 : ℝ) (751109 / 200000000 : ℝ) (2322457 / 3125000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (241 / 800 : ℝ)) (1826679 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (121 / 400 : ℝ) (676619 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (121 / 400 : ℝ))) h 2
    have he :
        (Real.exp (121 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (121 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1826679 / 1000000 : ℝ) - (121 / 400 : ℝ) / 2) / 32)
      (14883377 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_242 :
    ∀ u : ℝ, (121 / 400 : ℝ) ≤ u → u ≤ (243 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (7373659 / 10000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (121 / 400 : ℝ) (243 / 800 : ℝ) (457813 / 250000 : ℝ) (1835838014761 / 1000000000000 : ℝ)
    (11911813 / 10000000 : ℝ) (1852159 / 500000000 : ℝ) (7373659 / 10000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (121 / 400 : ℝ)) (457813 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (243 / 800 : ℝ) (1354931 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (243 / 800 : ℝ))) h 2
    have he :
        (Real.exp (243 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (243 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (457813 / 250000 : ℝ) - (243 / 800 : ℝ) / 2) / 32)
      (11911813 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_243 :
    ∀ u : ℝ, (243 / 800 : ℝ) ≤ u → u ≤ (61 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (4572271 / 6250000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (243 / 800 : ℝ) (61 / 200 : ℝ) (458959 / 250000 : ℝ) (460108525969 / 250000000000 : ℝ)
    (23833879 / 20000000 : ℝ) (36536631 / 10000000000 : ℝ) (4572271 / 6250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (243 / 800 : ℝ)) (458959 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (61 / 200 : ℝ) (678313 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (61 / 200 : ℝ))) h 2
    have he :
        (Real.exp (61 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (61 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (458959 / 250000 : ℝ) - (61 / 200 : ℝ) / 2) / 32)
      (23833879 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_244 :
    ∀ u : ℝ, (61 / 200 : ℝ) ≤ u → u ≤ (49 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (7257763 / 10000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (61 / 200 : ℝ) (49 / 160 : ℝ) (1840431 / 1000000 : ℝ) (461259663921 / 250000000000 : ℝ)
    (11922081 / 10000000 : ℝ) (9008943 / 2500000000 : ℝ) (7257763 / 10000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (61 / 200 : ℝ)) (1840431 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (49 / 160 : ℝ) (679161 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (49 / 160 : ℝ))) h 2
    have he :
        (Real.exp (49 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (49 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1840431 / 1000000 : ℝ) - (49 / 160 : ℝ) / 2) / 32)
      (11922081 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_245 :
    ∀ u : ℝ, (49 / 160 : ℝ) ≤ u → u ≤ (123 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (36000407 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (49 / 160 : ℝ) (123 / 400 : ℝ) (922519 / 500000 : ℝ) (1849657120441 / 1000000000000 : ℝ)
    (29818097 / 25000000 : ℝ) (7108087 / 2000000000 : ℝ) (36000407 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (49 / 160 : ℝ)) (922519 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (123 / 400 : ℝ) (1360021 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (123 / 400 : ℝ))) h 2
    have he :
        (Real.exp (123 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (123 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (922519 / 500000 : ℝ) - (123 / 400 : ℝ) / 2) / 32)
      (29818097 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_246 :
    ∀ u : ℝ, (123 / 400 : ℝ) ≤ u → u ≤ (247 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (71425903 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (123 / 400 : ℝ) (247 / 800 : ℝ) (231207 / 125000 : ℝ) (463571701321 / 250000000000 : ℝ)
    (29831029 / 25000000 : ℝ) (35050707 / 10000000000 : ℝ) (71425903 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (123 / 400 : ℝ)) (231207 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (247 / 800 : ℝ) (680861 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (247 / 800 : ℝ))) h 2
    have he :
        (Real.exp (247 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (247 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (231207 / 125000 : ℝ) - (247 / 800 : ℝ) / 2) / 32)
      (29831029 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_247 :
    ∀ u : ℝ, (247 / 800 : ℝ) ≤ u → u ≤ (31 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (70852929 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (247 / 800 : ℝ) (31 / 100 : ℝ) (927143 / 500000 : ℝ) (464732614369 / 250000000000 : ℝ)
    (14922001 / 12500000 : ℝ) (2160401 / 625000000 : ℝ) (70852929 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (247 / 800 : ℝ)) (927143 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (31 / 100 : ℝ) (681713 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (31 / 100 : ℝ))) h 2
    have he :
        (Real.exp (31 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (31 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (927143 / 500000 : ℝ) - (31 / 100 : ℝ) / 2) / 32)
      (14922001 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_248 :
    ∀ u : ℝ, (31 / 100 : ℝ) ≤ u → u ≤ (249 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (14056277 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (31 / 100 : ℝ) (249 / 800 : ℝ) (116183 / 62500 : ℝ) (1863582647161 / 1000000000000 : ℝ)
    (119428063 / 100000000 : ℝ) (34087533 / 10000000000 : ℝ) (14056277 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (31 / 100 : ℝ)) (116183 / 62500 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (249 / 800 : ℝ) (1365131 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (249 / 800 : ℝ))) h 2
    have he :
        (Real.exp (249 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (249 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (116183 / 62500 : ℝ) - (249 / 800 : ℝ) / 2) / 32)
      (119428063 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_249 :
    ∀ u : ℝ, (249 / 800 : ℝ) ≤ u → u ≤ (5 / 16 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (69711811 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (249 / 800 : ℝ) (5 / 16 : ℝ) (1863581 / 1000000 : ℝ) (467061529561 / 250000000000 : ℝ)
    (11948027 / 10000000 : ℝ) (33614121 / 10000000000 : ℝ) (69711811 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (249 / 800 : ℝ)) (1863581 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (5 / 16 : ℝ) (683419 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (5 / 16 : ℝ))) h 2
    have he :
        (Real.exp (5 / 16 : ℝ)) ^ 2 =
          Real.exp (2 * (5 / 16 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1863581 / 1000000 : ℝ) - (5 / 16 : ℝ) / 2) / 32)
      (11948027 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_250 :
    ∀ u : ℝ, (5 / 16 : ℝ) ≤ u → u ≤ (251 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (69144507 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (5 / 16 : ℝ) (251 / 800 : ℝ) (373649 / 200000 : ℝ) (117057726769 / 62500000000 : ℝ)
    (119532629 / 100000000 : ℝ) (33146137 / 10000000000 : ℝ) (69144507 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (5 / 16 : ℝ)) (373649 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (251 / 800 : ℝ) (342137 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (251 / 800 : ℝ))) h 2
    have he :
        (Real.exp (251 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (251 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (373649 / 200000 : ℝ) - (251 / 800 : ℝ) / 2) / 32)
      (119532629 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_251 :
    ∀ u : ℝ, (251 / 800 : ℝ) ≤ u → u ≤ (63 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (68578783 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (251 / 800 : ℝ) (63 / 200 : ℝ) (936461 / 500000 : ℝ) (4694031169 / 2500000000 : ℝ)
    (119585163 / 100000000 : ℝ) (32683339 / 10000000000 : ℝ) (68578783 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (251 / 800 : ℝ)) (936461 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (63 / 200 : ℝ) (68513 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (63 / 200 : ℝ))) h 2
    have he :
        (Real.exp (63 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (63 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (936461 / 500000 : ℝ) - (63 / 200 : ℝ) / 2) / 32)
      (119585163 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_252 :
    ∀ u : ℝ, (63 / 200 : ℝ) ≤ u → u ≤ (253 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (850189 / 1250000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (63 / 200 : ℝ) (253 / 800 : ℝ) (187761 / 100000 : ℝ) (470578164169 / 250000000000 : ℝ)
    (119637849 / 100000000 : ℝ) (32225891 / 10000000000 : ℝ) (850189 / 1250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (63 / 200 : ℝ)) (187761 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (253 / 800 : ℝ) (685987 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (253 / 800 : ℝ))) h 2
    have he :
        (Real.exp (253 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (253 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (187761 / 100000 : ℝ) - (253 / 800 : ℝ) / 2) / 32)
      (119637849 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_253 :
    ∀ u : ℝ, (253 / 800 : ℝ) ≤ u → u ≤ (127 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (33726651 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (253 / 800 : ℝ) (127 / 400 : ℝ) (188231 / 100000 : ℝ) (18870242161 / 10000000000 : ℝ)
    (1196907 / 1000000 : ℝ) (31773641 / 10000000000 : ℝ) (33726651 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (253 / 800 : ℝ)) (188231 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (127 / 400 : ℝ) (137369 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (127 / 400 : ℝ))) h 2
    have he :
        (Real.exp (127 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (127 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (188231 / 100000 : ℝ) - (127 / 400 : ℝ) / 2) / 32)
      (1196907 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_254 :
    ∀ u : ℝ, (127 / 400 : ℝ) ≤ u → u ≤ (51 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (8361673 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (127 / 400 : ℝ) (51 / 160 : ℝ) (943511 / 500000 : ℝ) (7389637369 / 3906250000 : ℝ)
    (23948743 / 20000000 : ℝ) (31326561 / 10000000000 : ℝ) (8361673 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (127 / 400 : ℝ)) (943511 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (51 / 160 : ℝ) (85963 / 62500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (51 / 160 : ℝ))) h 2
    have he :
        (Real.exp (51 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (51 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (943511 / 500000 : ℝ) - (51 / 160 : ℝ) / 2) / 32)
      (23948743 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_255 :
    ∀ u : ℝ, (51 / 160 : ℝ) ≤ u → u ≤ (8 / 25 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (33167811 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (51 / 160 : ℝ) (8 / 25 : ℝ) (378349 / 200000 : ℝ) (29632523881 / 15625000000 : ℝ)
    (59898441 / 50000000 : ℝ) (30884711 / 10000000000 : ℝ) (33167811 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (51 / 160 : ℝ)) (378349 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (8 / 25 : ℝ) (172141 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (8 / 25 : ℝ))) h 2
    have he :
        (Real.exp (8 / 25 : ℝ)) ^ 2 =
          Real.exp (2 * (8 / 25 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (378349 / 200000 : ℝ) - (8 / 25 : ℝ) / 2) / 32)
      (59898441 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_256 :
    ∀ u : ℝ, (8 / 25 : ℝ) ≤ u → u ≤ (257 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (32890029 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (8 / 25 : ℝ) (257 / 800 : ℝ) (11853 / 6250 : ℝ) (1901230080201 / 1000000000000 : ℝ)
    (59925107 / 50000000 : ℝ) (30447943 / 10000000000 : ℝ) (32890029 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (8 / 25 : ℝ)) (11853 / 6250 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (257 / 800 : ℝ) (1378851 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (257 / 800 : ℝ))) h 2
    have he :
        (Real.exp (257 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (257 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (11853 / 6250 : ℝ) - (257 / 800 : ℝ) / 2) / 32)
      (59925107 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_257 :
    ∀ u : ℝ, (257 / 800 : ℝ) ≤ u → u ≤ (129 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (3261299 / 5000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (257 / 800 : ℝ) (129 / 400 : ℝ) (475307 / 250000 : ℝ) (3049579729 / 1600000000 : ℝ)
    (29975931 / 25000000 : ℝ) (30016117 / 10000000000 : ℝ) (3261299 / 5000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (257 / 800 : ℝ)) (475307 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (129 / 400 : ℝ) (55223 / 40000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (129 / 400 : ℝ))) h 2
    have he :
        (Real.exp (129 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (129 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (475307 / 250000 : ℝ) - (129 / 400 : ℝ) / 2) / 32)
      (29975931 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_258 :
    ∀ u : ℝ, (129 / 400 : ℝ) ≤ u → u ≤ (259 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (80843 / 125000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (129 / 400 : ℝ) (259 / 800 : ℝ) (1905987 / 1000000 : ℝ) (477689704801 / 250000000000 : ℝ)
    (59978693 / 50000000 : ℝ) (7397351 / 2500000000 : ℝ) (80843 / 125000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (129 / 400 : ℝ)) (1905987 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (259 / 800 : ℝ) (691151 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (259 / 800 : ℝ))) h 2
    have he :
        (Real.exp (259 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (259 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1905987 / 1000000 : ℝ) - (259 / 800 : ℝ) / 2) / 32)
      (59978693 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_259 :
    ∀ u : ℝ, (259 / 800 : ℝ) ≤ u → u ≤ (13 / 40 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (64125057 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (259 / 800 : ℝ) (13 / 40 : ℝ) (1910757 / 1000000 : ℝ) (1915541808961 / 1000000000000 : ℝ)
    (60005601 / 50000000 : ℝ) (14583873 / 5000000000 : ℝ) (64125057 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (259 / 800 : ℝ)) (1910757 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (13 / 40 : ℝ) (1384031 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (13 / 40 : ℝ))) h 2
    have he :
        (Real.exp (13 / 40 : ℝ)) ^ 2 =
          Real.exp (2 * (13 / 40 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1910757 / 1000000 : ℝ) - (13 / 40 : ℝ) / 2) / 32)
      (60005601 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_240
#print axioms hpThetaEnergyUpper_interval_259

end HodgeProofHP
