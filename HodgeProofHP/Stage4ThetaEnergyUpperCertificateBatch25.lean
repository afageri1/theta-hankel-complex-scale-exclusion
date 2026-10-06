import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_500 :
    ∀ u : ℝ, (5 / 8 : ℝ) ≤ u → u ≤ (501 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2003919 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (5 / 8 : ℝ) (501 / 800 : ℝ) (1745171 / 500000 : ℝ) (3499080759889 / 1000000000000 : ℝ)
    (13947353 / 10000000 : ℝ) (59457 / 2500000000 : ℝ) (2003919 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (5 / 8 : ℝ)) (1745171 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (501 / 800 : ℝ) (1870583 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (501 / 800 : ℝ))) h 2
    have he :
        (Real.exp (501 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (501 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1745171 / 500000 : ℝ) - (501 / 800 : ℝ) / 2) / 32)
      (13947353 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_501 :
    ∀ u : ℝ, (501 / 800 : ℝ) ≤ u → u ≤ (251 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (980729 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (501 / 800 : ℝ) (251 / 400 : ℝ) (3499079 / 1000000 : ℝ) (3507840563929 / 1000000000000 : ℝ)
    (34897607 / 25000000 : ℝ) (231537 / 10000000000 : ℝ) (980729 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (501 / 800 : ℝ)) (3499079 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (251 / 400 : ℝ) (1872923 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (251 / 400 : ℝ))) h 2
    have he :
        (Real.exp (251 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (251 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3499079 / 1000000 : ℝ) - (251 / 400 : ℝ) / 2) / 32)
      (34897607 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_502 :
    ∀ u : ℝ, (251 / 400 : ℝ) ≤ u → u ≤ (503 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (479941 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (251 / 400 : ℝ) (503 / 800 : ℝ) (1753919 / 500000 : ℝ) (879155642689 / 250000000000 : ℝ)
    (69853863 / 50000000 : ℝ) (225397 / 10000000000 : ℝ) (479941 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (251 / 400 : ℝ)) (1753919 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (503 / 800 : ℝ) (937633 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (503 / 800 : ℝ))) h 2
    have he :
        (Real.exp (503 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (503 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1753919 / 500000 : ℝ) - (503 / 800 : ℝ) / 2) / 32)
      (69853863 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_503 :
    ∀ u : ℝ, (503 / 800 : ℝ) ≤ u → u ≤ (63 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (939411 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (503 / 800 : ℝ) (63 / 100 : ℝ) (1758309 / 500000 : ℝ) (3525423067321 / 1000000000000 : ℝ)
    (13982541 / 10000000 : ℝ) (43881 / 2000000000 : ℝ) (939411 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (503 / 800 : ℝ)) (1758309 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (63 / 100 : ℝ) (1877611 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (63 / 100 : ℝ))) h 2
    have he :
        (Real.exp (63 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (63 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1758309 / 500000 : ℝ) - (63 / 100 : ℝ) / 2) / 32)
      (13982541 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_504 :
    ∀ u : ℝ, (63 / 100 : ℝ) ≤ u → u ≤ (101 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1838617 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (63 / 100 : ℝ) (101 / 160 : ℝ) (3525421 / 1000000 : ℝ) (2208906001 / 625000000 : ℝ)
    (139943509 / 100000000 : ℝ) (53389 / 2500000000 : ℝ) (1838617 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (63 / 100 : ℝ)) (3525421 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (101 / 160 : ℝ) (46999 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (101 / 160 : ℝ))) h 2
    have he :
        (Real.exp (101 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (101 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3525421 / 1000000 : ℝ) - (101 / 160 : ℝ) / 2) / 32)
      (139943509 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_505 :
    ∀ u : ℝ, (101 / 160 : ℝ) ≤ u → u ≤ (253 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1799153 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (101 / 160 : ℝ) (253 / 400 : ℝ) (1767123 / 500000 : ℝ) (3543094700721 / 1000000000000 : ℝ)
    (140062011 / 100000000 : ℝ) (4157 / 200000000 : ℝ) (1799153 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (101 / 160 : ℝ)) (1767123 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (253 / 400 : ℝ) (1882311 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (253 / 400 : ℝ))) h 2
    have he :
        (Real.exp (253 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (253 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1767123 / 500000 : ℝ) - (253 / 400 : ℝ) / 2) / 32)
      (140062011 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_506 :
    ∀ u : ℝ, (253 / 400 : ℝ) ≤ u → u ≤ (507 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (176041 / 10000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (253 / 400 : ℝ) (507 / 800 : ℝ) (885773 / 250000 : ℝ) (142078486489 / 40000000000 : ℝ)
    (140180901 / 100000000 : ℝ) (101141 / 5000000000 : ℝ) (176041 / 10000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (253 / 400 : ℝ)) (885773 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (507 / 800 : ℝ) (376933 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (507 / 800 : ℝ))) h 2
    have he :
        (Real.exp (507 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (507 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (885773 / 250000 : ℝ) - (507 / 800 : ℝ) / 2) / 32)
      (140180901 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_507 :
    ∀ u : ℝ, (507 / 800 : ℝ) ≤ u → u ≤ (127 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (430597 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (507 / 800 : ℝ) (127 / 200 : ℝ) (3551961 / 1000000 : ℝ) (3560855802529 / 1000000000000 : ℝ)
    (14030021 / 10000000 : ℝ) (3937 / 200000000 : ℝ) (430597 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (507 / 800 : ℝ)) (3551961 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (127 / 200 : ℝ) (1887023 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (127 / 200 : ℝ))) h 2
    have he :
        (Real.exp (127 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (127 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3551961 / 1000000 : ℝ) - (127 / 200 : ℝ) / 2) / 32)
      (14030021 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_508 :
    ∀ u : ℝ, (127 / 200 : ℝ) ≤ u → u ≤ (509 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1685059 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (127 / 200 : ℝ) (509 / 800 : ℝ) (890213 / 250000 : ℝ) (3569768120689 / 1000000000000 : ℝ)
    (70209961 / 50000000 : ℝ) (3831 / 200000000 : ℝ) (1685059 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (127 / 200 : ℝ)) (890213 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (509 / 800 : ℝ) (1889383 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (509 / 800 : ℝ))) h 2
    have he :
        (Real.exp (509 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (509 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (890213 / 250000 : ℝ) - (509 / 800 : ℝ) / 2) / 32)
      (70209961 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_509 :
    ∀ u : ℝ, (509 / 800 : ℝ) ≤ u → u ≤ (51 / 80 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (824213 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (509 / 800 : ℝ) (51 / 80 : ℝ) (713953 / 200000 : ℝ) (894675732129 / 250000000000 : ℝ)
    (140540041 / 100000000 : ℝ) (9319 / 500000000 : ℝ) (824213 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (509 / 800 : ℝ)) (713953 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (51 / 80 : ℝ) (945873 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (51 / 80 : ℝ))) h 2
    have he :
        (Real.exp (51 / 80 : ℝ)) ^ 2 =
          Real.exp (2 * (51 / 80 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (713953 / 200000 : ℝ) - (51 / 80 : ℝ) / 2) / 32)
      (140540041 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_510 :
    ∀ u : ℝ, (51 / 80 : ℝ) ≤ u → u ≤ (511 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (806233 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (51 / 80 : ℝ) (511 / 800 : ℝ) (3578701 / 1000000 : ℝ) (3503574481 / 976562500 : ℝ)
    (140660579 / 100000000 : ℝ) (22667 / 1250000000 : ℝ) (806233 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (51 / 80 : ℝ)) (3578701 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (511 / 800 : ℝ) (59191 / 31250 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (511 / 800 : ℝ))) h 2
    have he :
        (Real.exp (511 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (511 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3578701 / 1000000 : ℝ) - (511 / 800 : ℝ) / 2) / 32)
      (140660579 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_511 :
    ∀ u : ℝ, (511 / 800 : ℝ) ≤ u → u ≤ (16 / 25 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1577187 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (511 / 800 : ℝ) (16 / 25 : ℝ) (3587659 / 1000000 : ℝ) (3596640183361 / 1000000000000 : ℝ)
    (5631261 / 4000000 : ℝ) (176417 / 10000000000 : ℝ) (1577187 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (511 / 800 : ℝ)) (3587659 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (16 / 25 : ℝ) (1896481 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (16 / 25 : ℝ))) h 2
    have he :
        (Real.exp (16 / 25 : ℝ)) ^ 2 =
          Real.exp (2 * (16 / 25 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3587659 / 1000000 : ℝ) - (16 / 25 : ℝ) / 2) / 32)
      (5631261 / 4000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_512 :
    ∀ u : ℝ, (16 / 25 : ℝ) ≤ u → u ≤ (513 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1542567 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (16 / 25 : ℝ) (513 / 800 : ℝ) (3596639 / 1000000 : ℝ) (3605642715609 / 1000000000000 : ℝ)
    (140902879 / 100000000 : ℝ) (171619 / 10000000000 : ℝ) (1542567 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (16 / 25 : ℝ)) (3596639 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (513 / 800 : ℝ) (1898853 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (513 / 800 : ℝ))) h 2
    have he :
        (Real.exp (513 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (513 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3596639 / 1000000 : ℝ) - (513 / 800 : ℝ) / 2) / 32)
      (140902879 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_513 :
    ∀ u : ℝ, (513 / 800 : ℝ) ≤ u → u ≤ (257 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (377151 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (513 / 800 : ℝ) (257 / 400 : ℝ) (1802821 / 500000 : ℝ) (3614671710441 / 1000000000000 : ℝ)
    (8814041 / 6250000 : ℝ) (8347 / 500000000 : ℝ) (377151 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (513 / 800 : ℝ)) (1802821 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (257 / 400 : ℝ) (1901229 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (257 / 400 : ℝ))) h 2
    have he :
        (Real.exp (257 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (257 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1802821 / 500000 : ℝ) - (257 / 400 : ℝ) / 2) / 32)
      (8814041 / 6250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_514 :
    ∀ u : ℝ, (257 / 400 : ℝ) ≤ u → u ≤ (103 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (18441 / 1250000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (257 / 400 : ℝ) (103 / 160 : ℝ) (3614667 / 1000000 : ℝ) (3623719610449 / 1000000000000 : ℝ)
    (141146843 / 100000000 : ℝ) (162377 / 10000000000 : ℝ) (18441 / 1250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (257 / 400 : ℝ)) (3614667 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (103 / 160 : ℝ) (1903607 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (103 / 160 : ℝ))) h 2
    have he :
        (Real.exp (103 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (103 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3614667 / 1000000 : ℝ) - (103 / 160 : ℝ) / 2) / 32)
      (141146843 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_515 :
    ∀ u : ℝ, (103 / 160 : ℝ) ≤ u → u ≤ (129 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1442583 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (103 / 160 : ℝ) (129 / 200 : ℝ) (724743 / 200000 : ℝ) (227049391009 / 62500000000 : ℝ)
    (28253891 / 20000000 : ℝ) (157927 / 10000000000 : ℝ) (1442583 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (103 / 160 : ℝ)) (724743 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (129 / 200 : ℝ) (476497 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (129 / 200 : ℝ))) h 2
    have he :
        (Real.exp (129 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (129 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (724743 / 200000 : ℝ) - (129 / 200 : ℝ) / 2) / 32)
      (28253891 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_516 :
    ∀ u : ℝ, (129 / 200 : ℝ) ≤ u → u ≤ (517 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (352627 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (129 / 200 : ℝ) (517 / 800 : ℝ) (1816393 / 500000 : ℝ) (227617730649 / 62500000000 : ℝ)
    (35348123 / 25000000 : ℝ) (38397 / 2500000000 : ℝ) (352627 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (129 / 200 : ℝ)) (1816393 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (517 / 800 : ℝ) (477093 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (517 / 800 : ℝ))) h 2
    have he :
        (Real.exp (517 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (517 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1816393 / 500000 : ℝ) - (517 / 800 : ℝ) / 2) / 32)
      (35348123 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_517 :
    ∀ u : ℝ, (517 / 800 : ℝ) ≤ u → u ≤ (259 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (172381 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (517 / 800 : ℝ) (259 / 400 : ℝ) (3641879 / 1000000 : ℝ) (912749033641 / 250000000000 : ℝ)
    (70757971 / 50000000 : ℝ) (74679 / 5000000000 : ℝ) (172381 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (517 / 800 : ℝ)) (3641879 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (259 / 400 : ℝ) (955379 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (259 / 400 : ℝ))) h 2
    have he :
        (Real.exp (259 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (259 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3641879 / 1000000 : ℝ) - (259 / 400 : ℝ) / 2) / 32)
      (70757971 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_518 :
    ∀ u : ℝ, (259 / 400 : ℝ) ≤ u → u ≤ (519 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1348203 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (259 / 400 : ℝ) (519 / 800 : ℝ) (730199 / 200000 : ℝ) (228758454369 / 62500000000 : ℝ)
    (141639819 / 100000000 : ℝ) (29047 / 2000000000 : ℝ) (1348203 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (259 / 400 : ℝ)) (730199 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (519 / 800 : ℝ) (478287 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (519 / 800 : ℝ))) h 2
    have he :
        (Real.exp (519 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (519 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (730199 / 200000 : ℝ) - (519 / 800 : ℝ) / 2) / 32)
      (141639819 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_519 :
    ∀ u : ℝ, (519 / 800 : ℝ) ≤ u → u ≤ (13 / 20 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (82371 / 6250000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (519 / 800 : ℝ) (13 / 20 : ℝ) (1830067 / 500000 : ℝ) (3669297322681 / 1000000000000 : ℝ)
    (35441031 / 25000000 : ℝ) (70607 / 5000000000 : ℝ) (82371 / 6250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (519 / 800 : ℝ)) (1830067 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (13 / 20 : ℝ) (1915541 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (13 / 20 : ℝ))) h 2
    have he :
        (Real.exp (13 / 20 : ℝ)) ^ 2 =
          Real.exp (2 * (13 / 20 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1830067 / 500000 : ℝ) - (13 / 20 : ℝ) / 2) / 32)
      (35441031 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_500
#print axioms hpThetaEnergyUpper_interval_519

end HodgeProofHP
