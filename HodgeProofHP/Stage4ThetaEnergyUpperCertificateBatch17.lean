import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_340 :
    ∀ u : ℝ, (17 / 40 : ℝ) ≤ u → u ≤ (341 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (27888023 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (17 / 40 : ℝ) (341 / 800 : ℝ) (1169823 / 500000 : ℝ) (9162126961 / 3906250000 : ℝ)
    (1562147 / 1250000 : ℝ) (1995077 / 2500000000 : ℝ) (27888023 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (17 / 40 : ℝ)) (1169823 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (341 / 800 : ℝ) (95719 / 62500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (341 / 800 : ℝ))) h 2
    have he :
        (Real.exp (341 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (341 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1169823 / 500000 : ℝ) - (341 / 800 : ℝ) / 2) / 32)
      (1562147 / 1250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_341 :
    ∀ u : ℝ, (341 / 800 : ℝ) ≤ u → u ≤ (171 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (13775847 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (341 / 800 : ℝ) (171 / 400 : ℝ) (2345503 / 1000000 : ℝ) (5878442241 / 2500000000 : ℝ)
    (62520581 / 50000000 : ℝ) (3919891 / 5000000000 : ℝ) (13775847 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (341 / 800 : ℝ)) (2345503 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (171 / 400 : ℝ) (76671 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (171 / 400 : ℝ))) h 2
    have he :
        (Real.exp (171 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (171 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2345503 / 1000000 : ℝ) - (171 / 400 : ℝ) / 2) / 32)
      (62520581 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_342 :
    ∀ u : ℝ, (171 / 400 : ℝ) ≤ u → u ≤ (343 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1360907 / 5000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (171 / 400 : ℝ) (343 / 800 : ℝ) (1175687 / 500000 : ℝ) (589315693561 / 250000000000 : ℝ)
    (62555387 / 50000000 : ℝ) (7701393 / 10000000000 : ℝ) (1360907 / 5000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (171 / 400 : ℝ)) (1175687 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (343 / 800 : ℝ) (767669 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (343 / 800 : ℝ))) h 2
    have he :
        (Real.exp (343 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (343 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1175687 / 500000 : ℝ) - (343 / 800 : ℝ) / 2) / 32)
      (62555387 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_343 :
    ∀ u : ℝ, (343 / 800 : ℝ) ≤ u → u ≤ (43 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (6721817 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (343 / 800 : ℝ) (43 / 100 : ℝ) (117863 / 50000 : ℝ) (590790539641 / 250000000000 : ℝ)
    (125180609 / 100000000 : ℝ) (756509 / 1000000000 : ℝ) (6721817 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (343 / 800 : ℝ)) (117863 / 50000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (43 / 100 : ℝ) (768629 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (43 / 100 : ℝ))) h 2
    have he :
        (Real.exp (43 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (43 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (117863 / 50000 : ℝ) - (43 / 100 : ℝ) / 2) / 32)
      (125180609 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_344 :
    ∀ u : ℝ, (43 / 100 : ℝ) ≤ u → u ≤ (69 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (13279623 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (43 / 100 : ℝ) (69 / 160 : ℝ) (59079 / 25000 : ℝ) (2369078150761 / 1000000000000 : ℝ)
    (3914083 / 3125000 : ℝ) (7430871 / 10000000000 : ℝ) (13279623 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (43 / 100 : ℝ)) (59079 / 25000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (69 / 160 : ℝ) (1539181 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (69 / 160 : ℝ))) h 2
    have he :
        (Real.exp (69 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (69 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (59079 / 25000 : ℝ) - (69 / 160 : ℝ) / 2) / 32)
      (3914083 / 3125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_345 :
    ∀ u : ℝ, (69 / 160 : ℝ) ≤ u → u ≤ (173 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (26233909 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (69 / 160 : ℝ) (173 / 400 : ℝ) (94763 / 40000 : ℝ) (593751925809 / 250000000000 : ℝ)
    (62660463 / 50000000 : ℝ) (7298691 / 10000000000 : ℝ) (26233909 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (69 / 160 : ℝ)) (94763 / 40000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (173 / 400 : ℝ) (770553 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (173 / 400 : ℝ))) h 2
    have he :
        (Real.exp (173 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (173 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (94763 / 40000 : ℝ) - (173 / 400 : ℝ) / 2) / 32)
      (62660463 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_346 :
    ∀ u : ℝ, (173 / 400 : ℝ) ≤ u → u ≤ (347 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (5182251 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (173 / 400 : ℝ) (347 / 800 : ℝ) (1187503 / 500000 : ℝ) (595238481289 / 250000000000 : ℝ)
    (15673929 / 12500000 : ℝ) (7168503 / 10000000000 : ℝ) (5182251 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (173 / 400 : ℝ)) (1187503 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (347 / 800 : ℝ) (771517 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (347 / 800 : ℝ))) h 2
    have he :
        (Real.exp (347 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (347 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1187503 / 500000 : ℝ) - (347 / 800 : ℝ) / 2) / 32)
      (15673929 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_347 :
    ∀ u : ℝ, (347 / 800 : ℝ) ≤ u → u ≤ (87 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (25591353 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (347 / 800 : ℝ) (87 / 200 : ℝ) (2380951 / 1000000 : ℝ) (149182110081 / 62500000000 : ℝ)
    (125462151 / 100000000 : ℝ) (281613 / 400000000 : ℝ) (25591353 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (347 / 800 : ℝ)) (2380951 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (87 / 200 : ℝ) (386241 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (87 / 200 : ℝ))) h 2
    have he :
        (Real.exp (87 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (87 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2380951 / 1000000 : ℝ) - (87 / 200 : ℝ) / 2) / 32)
      (125462151 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_348 :
    ∀ u : ℝ, (87 / 200 : ℝ) ≤ u → u ≤ (349 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (25274221 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (87 / 200 : ℝ) (349 / 800 : ℝ) (238691 / 100000 : ℝ) (9347215761 / 3906250000 : ℝ)
    (125533081 / 100000000 : ℝ) (3457069 / 5000000000 : ℝ) (25274221 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (87 / 200 : ℝ)) (238691 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (349 / 800 : ℝ) (96681 / 62500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (349 / 800 : ℝ))) h 2
    have he :
        (Real.exp (349 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (349 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (238691 / 100000 : ℝ) - (349 / 800 : ℝ) / 2) / 32)
      (125533081 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_349 :
    ∀ u : ℝ, (349 / 800 : ℝ) ≤ u → u ≤ (7 / 16 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (4991951 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (349 / 800 : ℝ) (7 / 16 : ℝ) (478577 / 200000 : ℝ) (2398877466561 / 1000000000000 : ℝ)
    (125604249 / 100000000 : ℝ) (678987 / 1000000000 : ℝ) (4991951 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (349 / 800 : ℝ)) (478577 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (7 / 16 : ℝ) (1548831 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (7 / 16 : ℝ))) h 2
    have he :
        (Real.exp (7 / 16 : ℝ)) ^ 2 =
          Real.exp (2 * (7 / 16 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (478577 / 200000 : ℝ) - (7 / 16 : ℝ) / 2) / 32)
      (125604249 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_350 :
    ∀ u : ℝ, (7 / 16 : ℝ) ≤ u → u ≤ (351 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (4929591 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (7 / 16 : ℝ) (351 / 800 : ℝ) (19191 / 8000 : ℝ) (9394067929 / 3906250000 : ℝ)
    (125675643 / 100000000 : ℝ) (5209 / 7812500 : ℝ) (4929591 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (7 / 16 : ℝ)) (19191 / 8000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (351 / 800 : ℝ) (96923 / 62500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (351 / 800 : ℝ))) h 2
    have he :
        (Real.exp (351 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (351 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (19191 / 8000 : ℝ) - (351 / 800 : ℝ) / 2) / 32)
      (125675643 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_351 :
    ∀ u : ℝ, (351 / 800 : ℝ) ≤ u → u ≤ (11 / 25 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (6084747 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (351 / 800 : ℝ) (11 / 25 : ℝ) (2404879 / 1000000 : ℝ) (150681383329 / 62500000000 : ℝ)
    (125747249 / 100000000 : ℝ) (6547089 / 10000000000 : ℝ) (6084747 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (351 / 800 : ℝ)) (2404879 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (11 / 25 : ℝ) (388177 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (11 / 25 : ℝ))) h 2
    have he :
        (Real.exp (11 / 25 : ℝ)) ^ 2 =
          Real.exp (2 * (11 / 25 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2404879 / 1000000 : ℝ) - (11 / 25 : ℝ) / 2) / 32)
      (125747249 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_352 :
    ∀ u : ℝ, (11 / 25 : ℝ) ≤ u → u ≤ (353 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (12016303 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (11 / 25 : ℝ) (353 / 800 : ℝ) (2410899 / 1000000 : ℝ) (966774649 / 400000000 : ℝ)
    (62909547 / 50000000 : ℝ) (642851 / 1000000000 : ℝ) (12016303 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (11 / 25 : ℝ)) (2410899 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (353 / 800 : ℝ) (31093 / 20000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (353 / 800 : ℝ))) h 2
    have he :
        (Real.exp (353 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (353 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2410899 / 1000000 : ℝ) - (353 / 800 : ℝ) / 2) / 32)
      (62909547 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_353 :
    ∀ u : ℝ, (353 / 800 : ℝ) ≤ u → u ≤ (177 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (296611 / 1250000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (353 / 800 : ℝ) (177 / 400 : ℝ) (1208467 / 500000 : ℝ) (605746220209 / 250000000000 : ℝ)
    (62945583 / 50000000 : ℝ) (315589 / 500000000 : ℝ) (296611 / 1250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (353 / 800 : ℝ)) (1208467 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (177 / 400 : ℝ) (778297 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (177 / 400 : ℝ))) h 2
    have he :
        (Real.exp (177 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (177 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1208467 / 500000 : ℝ) - (177 / 400 : ℝ) / 2) / 32)
      (62945583 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_354 :
    ∀ u : ℝ, (177 / 400 : ℝ) ≤ u → u ≤ (71 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (5856973 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (177 / 400 : ℝ) (71 / 160 : ℝ) (302873 / 125000 : ℝ) (2429050048681 / 1000000000000 : ℝ)
    (15745433 / 12500000 : ℝ) (6196879 / 10000000000 : ℝ) (5856973 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (177 / 400 : ℝ)) (302873 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (71 / 160 : ℝ) (1558541 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (71 / 160 : ℝ))) h 2
    have he :
        (Real.exp (71 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (71 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (302873 / 125000 : ℝ) - (71 / 160 : ℝ) / 2) / 32)
      (15745433 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_355 :
    ∀ u : ℝ, (71 / 160 : ℝ) ≤ u → u ≤ (89 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (23129631 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (71 / 160 : ℝ) (89 / 200 : ℝ) (2429049 / 1000000 : ℝ) (2435132161081 / 1000000000000 : ℝ)
    (126035989 / 100000000 : ℝ) (6083783 / 10000000000 : ℝ) (23129631 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (71 / 160 : ℝ)) (2429049 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (89 / 200 : ℝ) (1560491 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (89 / 200 : ℝ))) h 2
    have he :
        (Real.exp (89 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (89 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2429049 / 1000000 : ℝ) - (89 / 200 : ℝ) / 2) / 32)
      (126035989 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_356 :
    ∀ u : ℝ, (89 / 200 : ℝ) ≤ u → u ≤ (357 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (11417009 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (89 / 200 : ℝ) (357 / 800 : ℝ) (2435129 / 1000000 : ℝ) (2441228128249 / 1000000000000 : ℝ)
    (126108741 / 100000000 : ℝ) (597247 / 1000000000 : ℝ) (11417009 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (89 / 200 : ℝ)) (2435129 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (357 / 800 : ℝ) (1562443 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (357 / 800 : ℝ))) h 2
    have he :
        (Real.exp (357 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (357 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2435129 / 1000000 : ℝ) - (357 / 800 : ℝ) / 2) / 32)
      (126108741 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_357 :
    ∀ u : ℝ, (357 / 800 : ℝ) ≤ u → u ≤ (179 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (5635243 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (357 / 800 : ℝ) (179 / 400 : ℝ) (97649 / 40000 : ℝ) (2447337973609 / 1000000000000 : ℝ)
    (63090867 / 50000000 : ℝ) (2931449 / 5000000000 : ℝ) (5635243 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (357 / 800 : ℝ)) (97649 / 40000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (179 / 400 : ℝ) (1564397 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (179 / 400 : ℝ))) h 2
    have he :
        (Real.exp (179 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (179 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (97649 / 40000 : ℝ) - (179 / 400 : ℝ) / 2) / 32)
      (63090867 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_358 :
    ∀ u : ℝ, (179 / 400 : ℝ) ≤ u → u ≤ (359 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (22250711 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (179 / 400 : ℝ) (359 / 800 : ℝ) (489467 / 200000 : ℝ) (613366213329 / 250000000000 : ℝ)
    (63127471 / 50000000 : ℝ) (1438771 / 2500000000 : ℝ) (22250711 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (179 / 400 : ℝ)) (489467 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (359 / 800 : ℝ) (783177 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (359 / 800 : ℝ))) h 2
    have he :
        (Real.exp (359 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (359 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (489467 / 200000 : ℝ) - (359 / 800 : ℝ) / 2) / 32)
      (63127471 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_359 :
    ∀ u : ℝ, (359 / 800 : ℝ) ≤ u → u ≤ (9 / 20 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (5490753 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (359 / 800 : ℝ) (9 / 20 : ℝ) (2453461 / 1000000 : ℝ) (2459605665969 / 1000000000000 : ℝ)
    (126328391 / 100000000 : ℝ) (5648969 / 10000000000 : ℝ) (5490753 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (359 / 800 : ℝ)) (2453461 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (9 / 20 : ℝ) (1568313 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (9 / 20 : ℝ))) h 2
    have he :
        (Real.exp (9 / 20 : ℝ)) ^ 2 =
          Real.exp (2 * (9 / 20 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2453461 / 1000000 : ℝ) - (9 / 20 : ℝ) / 2) / 32)
      (126328391 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_340
#print axioms hpThetaEnergyUpper_interval_359

end HodgeProofHP
