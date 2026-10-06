import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_20 :
    ∀ u : ℝ, (1 / 40 : ℝ) ≤ u → u ≤ (21 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (90877709 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (1 / 40 : ℝ) (21 / 800 : ℝ) (1051271 / 1000000 : ℝ) (263475863401 / 250000000000 : ℝ)
    (110820967 / 100000000 : ℝ) (373334451 / 10000000000 : ℝ) (90877709 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (1 / 40 : ℝ)) (1051271 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (21 / 800 : ℝ) (513299 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (21 / 800 : ℝ))) h 2
    have he :
        (Real.exp (21 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (21 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1051271 / 1000000 : ℝ) - (21 / 800 : ℝ) / 2) / 32)
      (110820967 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_21 :
    ∀ u : ℝ, (21 / 800 : ℝ) ≤ u → u ≤ (11 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (11352883 / 6250000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (21 / 800 : ℝ) (11 / 400 : ℝ) (526951 / 500000 : ℝ) (264135351481 / 250000000000 : ℝ)
    (13855927 / 12500000 : ℝ) (185247199 / 5000000000 : ℝ) (11352883 / 6250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (21 / 800 : ℝ)) (526951 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (11 / 400 : ℝ) (513941 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (11 / 400 : ℝ))) h 2
    have he :
        (Real.exp (11 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (11 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (526951 / 500000 : ℝ) - (11 / 400 : ℝ) / 2) / 32)
      (13855927 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_22 :
    ∀ u : ℝ, (11 / 400 : ℝ) ≤ u → u ≤ (23 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (90765831 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (11 / 400 : ℝ) (23 / 800 : ℝ) (52827 / 50000 : ℝ) (4137448329 / 3906250000 : ℝ)
    (27718487 / 25000000 : ℝ) (367667813 / 10000000000 : ℝ) (90765831 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (11 / 400 : ℝ)) (52827 / 50000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (23 / 800 : ℝ) (64323 / 62500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (23 / 800 : ℝ))) h 2
    have he :
        (Real.exp (23 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (23 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (52827 / 50000 : ℝ) - (23 / 800 : ℝ) / 2) / 32)
      (27718487 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_23 :
    ∀ u : ℝ, (23 / 800 : ℝ) ≤ u → u ≤ (3 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (181410819 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (23 / 800 : ℝ) (3 / 100 : ℝ) (211837 / 200000 : ℝ) (42473500281 / 40000000000 : ℝ)
    (55450281 / 50000000 : ℝ) (91213707 / 2500000000 : ℝ) (181410819 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (23 / 800 : ℝ)) (211837 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (3 / 100 : ℝ) (206091 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (3 / 100 : ℝ))) h 2
    have he :
        (Real.exp (3 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (3 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (211837 / 200000 : ℝ) - (3 / 100 : ℝ) / 2) / 32)
      (55450281 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_24 :
    ∀ u : ℝ, (3 / 100 : ℝ) ≤ u → u ≤ (1 / 32 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (181285613 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (3 / 100 : ℝ) (1 / 32 : ℝ) (265459 / 250000 : ℝ) (259886641 / 244140625 : ℝ)
    (110927247 / 100000000 : ℝ) (45257077 / 1250000000 : ℝ) (181285613 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (3 / 100 : ℝ)) (265459 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (1 / 32 : ℝ) (16121 / 15625 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (1 / 32 : ℝ))) h 2
    have he :
        (Real.exp (1 / 32 : ℝ)) ^ 2 =
          Real.exp (2 * (1 / 32 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (265459 / 250000 : ℝ) - (1 / 32 : ℝ) / 2) / 32)
      (110927247 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_25 :
    ∀ u : ℝ, (1 / 32 : ℝ) ≤ u → u ≤ (13 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2830531 / 1562500 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (1 / 32 : ℝ) (13 / 400 : ℝ) (532247 / 500000 : ℝ) (266789811289 / 250000000000 : ℝ)
    (3467313 / 3125000 : ℝ) (179635913 / 5000000000 : ℝ) (2830531 / 1562500 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (1 / 32 : ℝ)) (532247 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (13 / 400 : ℝ) (516517 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (13 / 400 : ℝ))) h 2
    have he :
        (Real.exp (13 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (13 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (532247 / 500000 : ℝ) - (13 / 400 : ℝ) / 2) / 32)
      (3467313 / 3125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_26 :
    ∀ u : ℝ, (13 / 400 : ℝ) ≤ u → u ≤ (27 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (11313583 / 6250000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (13 / 400 : ℝ) (27 / 800 : ℝ) (1067159 / 1000000 : ℝ) (267457568569 / 250000000000 : ℝ)
    (110980867 / 100000000 : ℝ) (356500691 / 10000000000 : ℝ) (11313583 / 6250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (13 / 400 : ℝ)) (1067159 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (27 / 800 : ℝ) (517163 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (27 / 800 : ℝ))) h 2
    have he :
        (Real.exp (27 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (27 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1067159 / 1000000 : ℝ) - (27 / 800 : ℝ) / 2) / 32)
      (110980867 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_27 :
    ∀ u : ℝ, (27 / 800 : ℝ) ≤ u → u ≤ (7 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (180876321 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (27 / 800 : ℝ) (7 / 200 : ℝ) (106983 / 100000 : ℝ) (2681271961 / 2500000000 : ℝ)
    (11100779 / 10000000 : ℝ) (353744251 / 10000000000 : ℝ) (180876321 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (27 / 800 : ℝ)) (106983 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (7 / 200 : ℝ) (51781 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (7 / 200 : ℝ))) h 2
    have he :
        (Real.exp (7 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (7 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (106983 / 100000 : ℝ) - (7 / 200 : ℝ) / 2) / 32)
      (11100779 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_28 :
    ∀ u : ℝ, (7 / 200 : ℝ) ≤ u → u ≤ (29 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (45182581 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (7 / 200 : ℝ) (29 / 800 : ℝ) (268127 / 250000 : ℝ) (67199674441 / 62500000000 : ℝ)
    (22206959 / 20000000 : ℝ) (21937593 / 625000000 : ℝ) (45182581 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (7 / 200 : ℝ)) (268127 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (29 / 800 : ℝ) (259229 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (29 / 800 : ℝ))) h 2
    have he :
        (Real.exp (29 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (29 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (268127 / 250000 : ℝ) - (29 / 800 : ℝ) / 2) / 32)
      (22206959 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_29 :
    ∀ u : ℝ, (29 / 800 : ℝ) ≤ u → u ≤ (3 / 80 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (4514437 / 2500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (29 / 800 : ℝ) (3 / 80 : ℝ) (134399 / 125000 : ℝ) (67367759809 / 62500000000 : ℝ)
    (111061873 / 100000000 : ℝ) (174136663 / 5000000000 : ℝ) (4514437 / 2500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (29 / 800 : ℝ)) (134399 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (3 / 80 : ℝ) (259553 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (3 / 80 : ℝ))) h 2
    have he :
        (Real.exp (3 / 80 : ℝ)) ^ 2 =
          Real.exp (2 * (3 / 80 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (134399 / 125000 : ℝ) - (3 / 80 : ℝ) / 2) / 32)
      (111061873 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_30 :
    ∀ u : ℝ, (3 / 80 : ℝ) ≤ u → u ≤ (31 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (180420241 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (3 / 80 : ℝ) (31 / 800 : ℝ) (269471 / 250000 : ℝ) (1080583119121 / 1000000000000 : ℝ)
    (27772261 / 25000000 : ℝ) (43194721 / 1250000000 : ℝ) (180420241 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (3 / 80 : ℝ)) (269471 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (31 / 800 : ℝ) (1039511 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (31 / 800 : ℝ))) h 2
    have he :
        (Real.exp (31 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (31 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (269471 / 250000 : ℝ) - (31 / 800 : ℝ) / 2) / 32)
      (27772261 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_31 :
    ∀ u : ℝ, (31 / 800 : ℝ) ≤ u → u ≤ (1 / 25 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (36051491 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (31 / 800 : ℝ) (1 / 25 : ℝ) (540291 / 500000 : ℝ) (1083287537721 / 1000000000000 : ℝ)
    (434048 / 390625 : ℝ) (342856833 / 10000000000 : ℝ) (36051491 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (31 / 800 : ℝ)) (540291 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (1 / 25 : ℝ) (1040811 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (1 / 25 : ℝ))) h 2
    have he :
        (Real.exp (1 / 25 : ℝ)) ^ 2 =
          Real.exp (2 * (1 / 25 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (540291 / 500000 : ℝ) - (1 / 25 : ℝ) / 2) / 32)
      (434048 / 390625 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_32 :
    ∀ u : ℝ, (1 / 25 : ℝ) ≤ u → u ≤ (33 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (90044893 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (1 / 25 : ℝ) (33 / 800 : ℝ) (1083287 / 1000000 : ℝ) (1085999504769 / 1000000000000 : ℝ)
    (55571807 / 50000000 : ℝ) (340169631 / 10000000000 : ℝ) (90044893 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (1 / 25 : ℝ)) (1083287 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (33 / 800 : ℝ) (1042113 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (33 / 800 : ℝ))) h 2
    have he :
        (Real.exp (33 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (33 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1083287 / 1000000 : ℝ) - (33 / 800 : ℝ) / 2) / 32)
      (55571807 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_33 :
    ∀ u : ℝ, (33 / 800 : ℝ) ≤ u → u ≤ (17 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (3598357 / 2000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (33 / 800 : ℝ) (17 / 400 : ℝ) (542999 / 500000 : ℝ) (1088719035889 / 1000000000000 : ℝ)
    (111171013 / 100000000 : ℝ) (337497053 / 10000000000 : ℝ) (3598357 / 2000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (33 / 800 : ℝ)) (542999 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (17 / 400 : ℝ) (1043417 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (17 / 400 : ℝ))) h 2
    have he :
        (Real.exp (17 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (17 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (542999 / 500000 : ℝ) - (17 / 400 : ℝ) / 2) / 32)
      (111171013 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_34 :
    ∀ u : ℝ, (17 / 400 : ℝ) ≤ u → u ≤ (7 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (17973911 / 10000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (17 / 400 : ℝ) (7 / 160 : ℝ) (1088717 / 1000000 : ℝ) (272861014321 / 250000000000 : ℝ)
    (55599253 / 50000000 : ℝ) (41854633 / 1250000000 : ℝ) (17973911 / 10000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (17 / 400 : ℝ)) (1088717 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (7 / 160 : ℝ) (522361 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (7 / 160 : ℝ))) h 2
    have he :
        (Real.exp (7 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (7 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1088717 / 1000000 : ℝ) - (7 / 160 : ℝ) / 2) / 32)
      (55599253 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_35 :
    ∀ u : ℝ, (7 / 160 : ℝ) ≤ u → u ≤ (9 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (179554999 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (7 / 160 : ℝ) (9 / 200 : ℝ) (545721 / 500000 : ℝ) (68385911049 / 62500000000 : ℝ)
    (111226071 / 100000000 : ℝ) (332191809 / 10000000000 : ℝ) (179554999 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (7 / 160 : ℝ)) (545721 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (9 / 200 : ℝ) (261507 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (9 / 200 : ℝ))) h 2
    have he :
        (Real.exp (9 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (9 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (545721 / 500000 : ℝ) - (9 / 200 : ℝ) / 2) / 32)
      (111226071 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_36 :
    ∀ u : ℝ, (9 / 200 : ℝ) ≤ u → u ≤ (37 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (44841817 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (9 / 200 : ℝ) (37 / 800 : ℝ) (547087 / 500000 : ℝ) (1096914791569 / 1000000000000 : ℝ)
    (111253719 / 100000000 : ℝ) (41195029 / 1250000000 : ℝ) (44841817 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (9 / 200 : ℝ)) (547087 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (37 / 800 : ℝ) (1047337 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (37 / 800 : ℝ))) h 2
    have he :
        (Real.exp (37 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (37 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (547087 / 500000 : ℝ) - (37 / 800 : ℝ) / 2) / 32)
      (111253719 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_37 :
    ∀ u : ℝ, (37 / 800 : ℝ) ≤ u → u ≤ (19 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (7166941 / 4000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (37 / 800 : ℝ) (19 / 400 : ℝ) (1096913 / 1000000 : ℝ) (1099660530609 / 1000000000000 : ℝ)
    (2225629 / 2000000 : ℝ) (40867793 / 1250000000 : ℝ) (7166941 / 4000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (37 / 800 : ℝ)) (1096913 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (19 / 400 : ℝ) (1048647 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (19 / 400 : ℝ))) h 2
    have he :
        (Real.exp (19 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (19 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1096913 / 1000000 : ℝ) - (19 / 400 : ℝ) / 2) / 32)
      (2225629 / 2000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_38 :
    ∀ u : ℝ, (19 / 400 : ℝ) ≤ u → u ≤ (39 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (44743599 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (19 / 400 : ℝ) (39 / 800 : ℝ) (549829 / 500000 : ℝ) (275602950441 / 250000000000 : ℝ)
    (22261851 / 20000000 : ℝ) (324338997 / 10000000000 : ℝ) (44743599 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (19 / 400 : ℝ)) (549829 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (39 / 800 : ℝ) (524979 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (39 / 800 : ℝ))) h 2
    have he :
        (Real.exp (39 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (39 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (549829 / 500000 : ℝ) - (39 / 800 : ℝ) / 2) / 32)
      (22261851 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_39 :
    ∀ u : ℝ, (39 / 800 : ℝ) ≤ u → u ≤ (1 / 20 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (44692769 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (39 / 800 : ℝ) (1 / 20 : ℝ) (1102411 / 1000000 : ℝ) (17268325281 / 15625000000 : ℝ)
    (111337153 / 100000000 : ℝ) (321748421 / 10000000000 : ℝ) (44692769 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (39 / 800 : ℝ)) (1102411 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (1 / 20 : ℝ) (131409 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (1 / 20 : ℝ))) h 2
    have he :
        (Real.exp (1 / 20 : ℝ)) ^ 2 =
          Real.exp (2 * (1 / 20 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1102411 / 1000000 : ℝ) - (1 / 20 : ℝ) / 2) / 32)
      (111337153 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_20
#print axioms hpThetaEnergyUpper_interval_39

end HodgeProofHP
