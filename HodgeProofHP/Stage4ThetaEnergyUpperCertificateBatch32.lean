import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_640 :
    ∀ u : ℝ, (4 / 5 : ℝ) ≤ u → u ≤ (641 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (11663 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (4 / 5 : ℝ) (641 / 800 : ℝ) (4953031 / 1000000 : ℝ) (7944691689 / 1600000000 : ℝ)
    (80279929 / 50000000 : ℝ) (657 / 2500000000 : ℝ) (11663 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (4 / 5 : ℝ)) (4953031 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (641 / 800 : ℝ) (89133 / 40000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (641 / 800 : ℝ))) h 2
    have he :
        (Real.exp (641 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (641 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4953031 / 1000000 : ℝ) - (641 / 800 : ℝ) / 2) / 32)
      (80279929 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_641 :
    ∀ u : ℝ, (641 / 800 : ℝ) ≤ u → u ≤ (321 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (903 / 2000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (641 / 800 : ℝ) (321 / 400 : ℝ) (4965429 / 1000000 : ℝ) (77779074321 / 15625000000 : ℝ)
    (160752167 / 100000000 : ℝ) (253 / 1000000000 : ℝ) (903 / 2000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (641 / 800 : ℝ)) (4965429 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (321 / 400 : ℝ) (278889 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (321 / 400 : ℝ))) h 2
    have he :
        (Real.exp (321 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (321 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4965429 / 1000000 : ℝ) - (321 / 400 : ℝ) / 2) / 32)
      (160752167 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_642 :
    ∀ u : ℝ, (321 / 400 : ℝ) ≤ u → u ≤ (643 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (21833 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (321 / 400 : ℝ) (643 / 800 : ℝ) (2488929 / 500000 : ℝ) (4990322613409 / 1000000000000 : ℝ)
    (32189039 / 20000000 : ℝ) (1217 / 5000000000 : ℝ) (21833 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (321 / 400 : ℝ)) (2488929 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (643 / 800 : ℝ) (2233903 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (643 / 800 : ℝ))) h 2
    have he :
        (Real.exp (643 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (643 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2488929 / 500000 : ℝ) - (643 / 800 : ℝ) / 2) / 32)
      (32189039 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_643 :
    ∀ u : ℝ, (643 / 800 : ℝ) ≤ u → u ≤ (161 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (42237 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (643 / 800 : ℝ) (161 / 200 : ℝ) (4990319 / 1000000 : ℝ) (5002813469809 / 1000000000000 : ℝ)
    (80569481 / 50000000 : ℝ) (1171 / 5000000000 : ℝ) (42237 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (643 / 800 : ℝ)) (4990319 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (161 / 200 : ℝ) (2236697 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (161 / 200 : ℝ))) h 2
    have he :
        (Real.exp (161 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (161 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4990319 / 1000000 : ℝ) - (161 / 200 : ℝ) / 2) / 32)
      (80569481 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_644 :
    ∀ u : ℝ, (161 / 200 : ℝ) ≤ u → u ≤ (129 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1277 / 3125000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (161 / 200 : ℝ) (129 / 160 : ℝ) (500281 / 100000 : ℝ) (200613514201 / 40000000000 : ℝ)
    (161333437 / 100000000 : ℝ) (1127 / 5000000000 : ℝ) (1277 / 3125000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (161 / 200 : ℝ)) (500281 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (129 / 160 : ℝ) (447899 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (129 / 160 : ℝ))) h 2
    have he :
        (Real.exp (129 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (129 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (500281 / 100000 : ℝ) - (129 / 160 : ℝ) / 2) / 32)
      (161333437 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_645 :
    ∀ u : ℝ, (129 / 160 : ℝ) ≤ u → u ≤ (323 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (39513 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (129 / 160 : ℝ) (323 / 400 : ℝ) (5015333 / 1000000 : ℝ) (78560802369 / 15625000000 : ℝ)
    (161528653 / 100000000 : ℝ) (271 / 1250000000 : ℝ) (39513 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (129 / 160 : ℝ)) (5015333 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (323 / 400 : ℝ) (280287 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (323 / 400 : ℝ))) h 2
    have he :
        (Real.exp (323 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (323 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (5015333 / 1000000 : ℝ) - (323 / 400 : ℝ) / 2) / 32)
      (161528653 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_646 :
    ∀ u : ℝ, (323 / 400 : ℝ) ≤ u → u ≤ (647 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (38219 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (323 / 400 : ℝ) (647 / 800 : ℝ) (5027887 / 1000000 : ℝ) (504047401 / 100000000 : ℝ)
    (80862299 / 50000000 : ℝ) (1043 / 5000000000 : ℝ) (38219 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (323 / 400 : ℝ)) (5027887 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (647 / 800 : ℝ) (22451 / 10000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (647 / 800 : ℝ))) h 2
    have he :
        (Real.exp (647 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (647 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (5027887 / 1000000 : ℝ) - (647 / 800 : ℝ) / 2) / 32)
      (80862299 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_647 :
    ∀ u : ℝ, (647 / 800 : ℝ) ≤ u → u ≤ (81 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (36947 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (647 / 800 : ℝ) (81 / 100 : ℝ) (630059 / 125000 : ℝ) (315818148529 / 62500000000 : ℝ)
    (161921273 / 100000000 : ℝ) (1003 / 5000000000 : ℝ) (36947 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (647 / 800 : ℝ)) (630059 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (81 / 100 : ℝ) (561977 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (81 / 100 : ℝ))) h 2
    have he :
        (Real.exp (81 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (81 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (630059 / 125000 : ℝ) - (81 / 100 : ℝ) / 2) / 32)
      (161921273 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_648 :
    ∀ u : ℝ, (81 / 100 : ℝ) ≤ u → u ≤ (649 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (17867 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (81 / 100 : ℝ) (649 / 800 : ℝ) (5053089 / 1000000 : ℝ) (197880489 / 39062500 : ℝ)
    (20264837 / 12500000 : ℝ) (193 / 1000000000 : ℝ) (17867 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (81 / 100 : ℝ)) (5053089 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (649 / 800 : ℝ) (14067 / 6250 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (649 / 800 : ℝ))) h 2
    have he :
        (Real.exp (649 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (649 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (5053089 / 1000000 : ℝ) - (649 / 800 : ℝ) / 2) / 32)
      (20264837 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_649 :
    ∀ u : ℝ, (649 / 800 : ℝ) ≤ u → u ≤ (13 / 16 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (6909 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (649 / 800 : ℝ) (13 / 16 : ℝ) (2532869 / 500000 : ℝ) (203136799849 / 40000000000 : ℝ)
    (16231687 / 10000000 : ℝ) (29 / 156250000 : ℝ) (6909 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (649 / 800 : ℝ)) (2532869 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (13 / 16 : ℝ) (450707 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (13 / 16 : ℝ))) h 2
    have he :
        (Real.exp (13 / 16 : ℝ)) ^ 2 =
          Real.exp (2 * (13 / 16 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2532869 / 500000 : ℝ) - (13 / 16 : ℝ) / 2) / 32)
      (16231687 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_650 :
    ∀ u : ℝ, (13 / 16 : ℝ) ≤ u → u ≤ (651 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1669 / 5000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (13 / 16 : ℝ) (651 / 800 : ℝ) (2539209 / 500000 : ℝ) (1272783343329 / 250000000000 : ℝ)
    (8125789 / 5000000 : ℝ) (223 / 1250000000 : ℝ) (1669 / 5000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (13 / 16 : ℝ)) (2539209 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (651 / 800 : ℝ) (1128177 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (651 / 800 : ℝ))) h 2
    have he :
        (Real.exp (651 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (651 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2539209 / 500000 : ℝ) - (651 / 800 : ℝ) / 2) / 32)
      (8125789 / 5000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_651 :
    ∀ u : ℝ, (651 / 800 : ℝ) ≤ u → u ≤ (163 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (32277 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (651 / 800 : ℝ) (163 / 200 : ℝ) (509113 / 100000 : ℝ) (79748065609 / 15625000000 : ℝ)
    (32543089 / 20000000 : ℝ) (429 / 2500000000 : ℝ) (32277 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (651 / 800 : ℝ)) (509113 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (163 / 200 : ℝ) (282397 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (163 / 200 : ℝ))) h 2
    have he :
        (Real.exp (163 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (163 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (509113 / 100000 : ℝ) - (163 / 200 : ℝ) / 2) / 32)
      (32543089 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_652 :
    ∀ u : ℝ, (163 / 200 : ℝ) ≤ u → u ≤ (653 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1559 / 5000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (163 / 200 : ℝ) (653 / 800 : ℝ) (5103873 / 1000000 : ℝ) (1279163262001 / 250000000000 : ℝ)
    (162915851 / 100000000 : ℝ) (1649 / 10000000000 : ℝ) (1559 / 5000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (163 / 200 : ℝ)) (5103873 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (653 / 800 : ℝ) (1131001 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (653 / 800 : ℝ))) h 2
    have he :
        (Real.exp (653 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (653 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (5103873 / 1000000 : ℝ) - (653 / 800 : ℝ) / 2) / 32)
      (162915851 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_653 :
    ∀ u : ℝ, (653 / 800 : ℝ) ≤ u → u ≤ (327 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1883 / 6250000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (653 / 800 : ℝ) (327 / 400 : ℝ) (5116649 / 1000000 : ℝ) (5129459458561 / 1000000000000 : ℝ)
    (20389629 / 12500000 : ℝ) (317 / 2000000000 : ℝ) (1883 / 6250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (653 / 800 : ℝ)) (5116649 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (327 / 400 : ℝ) (2264831 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (327 / 400 : ℝ))) h 2
    have he :
        (Real.exp (327 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (327 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (5116649 / 1000000 : ℝ) - (327 / 400 : ℝ) / 2) / 32)
      (20389629 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_654 :
    ∀ u : ℝ, (327 / 400 : ℝ) ≤ u → u ≤ (131 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (29121 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (327 / 400 : ℝ) (131 / 160 : ℝ) (5129457 / 1000000 : ℝ) (20087109441 / 3906250000 : ℝ)
    (81659487 / 50000000 : ℝ) (381 / 2500000000 : ℝ) (29121 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (327 / 400 : ℝ)) (5129457 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (131 / 160 : ℝ) (141729 / 62500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (131 / 160 : ℝ))) h 2
    have he :
        (Real.exp (131 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (131 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (5129457 / 1000000 : ℝ) - (131 / 160 : ℝ) / 2) / 32)
      (81659487 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_655 :
    ∀ u : ℝ, (131 / 160 : ℝ) ≤ u → u ≤ (41 / 50 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (28141 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (131 / 160 : ℝ) (41 / 50 : ℝ) (642787 / 125000 : ℝ) (20620681 / 4000000 : ℝ)
    (163521663 / 100000000 : ℝ) (293 / 2000000000 : ℝ) (28141 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (131 / 160 : ℝ)) (642787 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (41 / 50 : ℝ) (4541 / 2000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (41 / 50 : ℝ))) h 2
    have he :
        (Real.exp (41 / 50 : ℝ)) ^ 2 =
          Real.exp (2 * (41 / 50 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (642787 / 125000 : ℝ) - (41 / 50 : ℝ) / 2) / 32)
      (163521663 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_656 :
    ∀ u : ℝ, (41 / 50 : ℝ) ≤ u → u ≤ (657 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (27189 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (41 / 50 : ℝ) (657 / 800 : ℝ) (161099 / 31250 : ℝ) (12920186889 / 2500000000 : ℝ)
    (81862567 / 50000000 : ℝ) (11 / 78125000 : ℝ) (27189 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (41 / 50 : ℝ)) (161099 / 31250 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (657 / 800 : ℝ) (113667 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (657 / 800 : ℝ))) h 2
    have he :
        (Real.exp (657 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (657 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (161099 / 31250 : ℝ) - (657 / 800 : ℝ) / 2) / 32)
      (81862567 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_657 :
    ∀ u : ℝ, (657 / 800 : ℝ) ≤ u → u ≤ (329 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (3283 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (657 / 800 : ℝ) (329 / 400 : ℝ) (646009 / 125000 : ℝ) (80953337529 / 15625000000 : ℝ)
    (163929373 / 100000000 : ℝ) (1353 / 10000000000 : ℝ) (3283 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (657 / 800 : ℝ)) (646009 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (329 / 400 : ℝ) (284523 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (329 / 400 : ℝ))) h 2
    have he :
        (Real.exp (329 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (329 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (646009 / 125000 : ℝ) - (329 / 400 : ℝ) / 2) / 32)
      (163929373 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_658 :
    ∀ u : ℝ, (329 / 400 : ℝ) ≤ u → u ≤ (659 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (3171 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (329 / 400 : ℝ) (659 / 800 : ℝ) (323813 / 62500 : ℝ) (5193982298961 / 1000000000000 : ℝ)
    (164134383 / 100000000 : ℝ) (13 / 100000000 : ℝ) (3171 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (329 / 400 : ℝ)) (323813 / 62500 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (659 / 800 : ℝ) (2279031 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (659 / 800 : ℝ))) h 2
    have he :
        (Real.exp (659 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (659 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (323813 / 62500 : ℝ) - (659 / 800 : ℝ) / 2) / 32)
      (164134383 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_659 :
    ∀ u : ℝ, (659 / 800 : ℝ) ≤ u → u ≤ (33 / 40 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (12241 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (659 / 800 : ℝ) (33 / 40 : ℝ) (5193977 / 1000000 : ℝ) (5206980898161 / 1000000000000 : ℝ)
    (164340181 / 100000000 : ℝ) (39 / 312500000 : ℝ) (12241 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (659 / 800 : ℝ)) (5193977 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (33 / 40 : ℝ) (2281881 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (33 / 40 : ℝ))) h 2
    have he :
        (Real.exp (33 / 40 : ℝ)) ^ 2 =
          Real.exp (2 * (33 / 40 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (5193977 / 1000000 : ℝ) - (33 / 40 : ℝ) / 2) / 32)
      (164340181 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_640
#print axioms hpThetaEnergyUpper_interval_659

end HodgeProofHP
