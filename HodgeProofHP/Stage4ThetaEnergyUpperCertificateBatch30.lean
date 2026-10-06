import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_600 :
    ∀ u : ℝ, (3 / 4 : ℝ) ≤ u → u ≤ (601 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (161839 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (3 / 4 : ℝ) (601 / 800 : ℝ) (560211 / 125000 : ℝ) (4387605121 / 976562500 : ℝ)
    (38355701 / 25000000 : ℝ) (563 / 500000000 : ℝ) (161839 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (3 / 4 : ℝ)) (560211 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (601 / 800 : ℝ) (66239 / 31250 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (601 / 800 : ℝ))) h 2
    have he :
        (Real.exp (601 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (601 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (560211 / 125000 : ℝ) - (601 / 800 : ℝ) / 2) / 32)
      (38355701 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_601 :
    ∀ u : ℝ, (601 / 800 : ℝ) ≤ u → u ≤ (301 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (39291 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (601 / 800 : ℝ) (301 / 400 : ℝ) (2246453 / 500000 : ℝ) (450415729 / 100000000 : ℝ)
    (7679439 / 5000000 : ℝ) (10877 / 10000000000 : ℝ) (39291 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (601 / 800 : ℝ)) (2246453 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (301 / 400 : ℝ) (21223 / 10000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (301 / 400 : ℝ))) h 2
    have he :
        (Real.exp (301 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (301 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2246453 / 500000 : ℝ) - (301 / 400 : ℝ) / 2) / 32)
      (7679439 / 5000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_602 :
    ∀ u : ℝ, (301 / 400 : ℝ) ≤ u → u ≤ (603 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (152609 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (301 / 400 : ℝ) (603 / 800 : ℝ) (4504153 / 1000000 : ℝ) (1128857375529 / 250000000000 : ℝ)
    (153755373 / 100000000 : ℝ) (5253 / 5000000000 : ℝ) (152609 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (301 / 400 : ℝ)) (4504153 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (603 / 800 : ℝ) (1062477 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (603 / 800 : ℝ))) h 2
    have he :
        (Real.exp (603 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (603 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4504153 / 1000000 : ℝ) - (603 / 800 : ℝ) / 2) / 32)
      (153755373 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_603 :
    ∀ u : ℝ, (603 / 800 : ℝ) ≤ u → u ≤ (151 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (148177 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (603 / 800 : ℝ) (151 / 200 : ℝ) (4515427 / 1000000 : ℝ) (282920801409 / 62500000000 : ℝ)
    (76961277 / 50000000 : ℝ) (10147 / 10000000000 : ℝ) (148177 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (603 / 800 : ℝ)) (4515427 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (151 / 200 : ℝ) (531903 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (151 / 200 : ℝ))) h 2
    have he :
        (Real.exp (151 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (151 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4515427 / 1000000 : ℝ) - (151 / 200 : ℝ) / 2) / 32)
      (76961277 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_604 :
    ∀ u : ℝ, (151 / 200 : ℝ) ≤ u → u ≤ (121 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (143869 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (151 / 200 : ℝ) (121 / 160 : ℝ) (452673 / 100000 : ℝ) (4538063054529 / 1000000000000 : ℝ)
    (38522589 / 25000000 : ℝ) (49 / 50000000 : ℝ) (143869 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (151 / 200 : ℝ)) (452673 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (121 / 160 : ℝ) (2130273 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (121 / 160 : ℝ))) h 2
    have he :
        (Real.exp (121 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (121 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (452673 / 100000 : ℝ) - (121 / 160 : ℝ) / 2) / 32)
      (38522589 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_605 :
    ∀ u : ℝ, (121 / 160 : ℝ) ≤ u → u ≤ (303 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (69829 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (121 / 160 : ℝ) (303 / 400 : ℝ) (4538061 / 1000000 : ℝ) (1137356127961 / 250000000000 : ℝ)
    (38564691 / 25000000 : ℝ) (9463 / 10000000000 : ℝ) (69829 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (121 / 160 : ℝ)) (4538061 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (303 / 400 : ℝ) (1066469 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (303 / 400 : ℝ))) h 2
    have he :
        (Real.exp (303 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (303 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4538061 / 1000000 : ℝ) - (303 / 400 : ℝ) / 2) / 32)
      (38564691 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_606 :
    ∀ u : ℝ, (303 / 400 : ℝ) ≤ u → u ≤ (607 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (67781 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (303 / 400 : ℝ) (607 / 800 : ℝ) (227471 / 50000 : ℝ) (1140203246809 / 250000000000 : ℝ)
    (154427781 / 100000000 : ℝ) (9137 / 10000000000 : ℝ) (67781 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (303 / 400 : ℝ)) (227471 / 50000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (607 / 800 : ℝ) (1067803 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (607 / 800 : ℝ))) h 2
    have he :
        (Real.exp (607 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (607 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (227471 / 50000 : ℝ) - (607 / 800 : ℝ) / 2) / 32)
      (154427781 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_607 :
    ∀ u : ℝ, (607 / 800 : ℝ) ≤ u → u ≤ (19 / 25 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (131583 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (607 / 800 : ℝ) (19 / 25 : ℝ) (570101 / 125000 : ℝ) (4572228528729 / 1000000000000 : ℝ)
    (154597423 / 100000000 : ℝ) (4411 / 5000000000 : ℝ) (131583 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (607 / 800 : ℝ)) (570101 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (19 / 25 : ℝ) (2138277 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (19 / 25 : ℝ))) h 2
    have he :
        (Real.exp (19 / 25 : ℝ)) ^ 2 =
          Real.exp (2 * (19 / 25 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (570101 / 125000 : ℝ) - (19 / 25 : ℝ) / 2) / 32)
      (154597423 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_608 :
    ∀ u : ℝ, (19 / 25 : ℝ) ≤ u → u ≤ (609 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (31923 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (19 / 25 : ℝ) (609 / 800 : ℝ) (71441 / 15625 : ℝ) (4583671184401 / 1000000000000 : ℝ)
    (154767677 / 100000000 : ℝ) (2129 / 2500000000 : ℝ) (31923 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (19 / 25 : ℝ)) (71441 / 15625 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (609 / 800 : ℝ) (2140951 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (609 / 800 : ℝ))) h 2
    have he :
        (Real.exp (609 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (609 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (71441 / 15625 : ℝ) - (609 / 800 : ℝ) / 2) / 32)
      (154767677 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_609 :
    ∀ u : ℝ, (609 / 800 : ℝ) ≤ u → u ≤ (61 / 80 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (123923 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (609 / 800 : ℝ) (61 / 80 : ℝ) (4583669 / 1000000 : ℝ) (4595145289641 / 1000000000000 : ℝ)
    (77469279 / 50000000 : ℝ) (8221 / 10000000000 : ℝ) (123923 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (609 / 800 : ℝ)) (4583669 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (61 / 80 : ℝ) (2143629 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (61 / 80 : ℝ))) h 2
    have he :
        (Real.exp (61 / 80 : ℝ)) ^ 2 =
          Real.exp (2 * (61 / 80 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4583669 / 1000000 : ℝ) - (61 / 80 : ℝ) / 2) / 32)
      (77469279 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_610 :
    ∀ u : ℝ, (61 / 80 : ℝ) ≤ u → u ≤ (611 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (24049 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (61 / 80 : ℝ) (611 / 800 : ℝ) (4595143 / 1000000 : ℝ) (46066466161 / 10000000000 : ℝ)
    (15511007 / 10000000 : ℝ) (1587 / 2000000000 : ℝ) (24049 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (61 / 80 : ℝ)) (4595143 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (611 / 800 : ℝ) (214631 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (611 / 800 : ℝ))) h 2
    have he :
        (Real.exp (611 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (611 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4595143 / 1000000 : ℝ) - (611 / 800 : ℝ) / 2) / 32)
      (15511007 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_611 :
    ∀ u : ℝ, (611 / 800 : ℝ) ≤ u → u ≤ (153 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (116663 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (611 / 800 : ℝ) (153 / 200 : ℝ) (921329 / 200000 : ℝ) (184727180401 / 40000000000 : ℝ)
    (155282199 / 100000000 : ℝ) (3829 / 5000000000 : ℝ) (116663 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (611 / 800 : ℝ)) (921329 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (153 / 200 : ℝ) (429799 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (153 / 200 : ℝ))) h 2
    have he :
        (Real.exp (153 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (153 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (921329 / 200000 : ℝ) - (153 / 200 : ℝ) / 2) / 32)
      (155282199 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_612 :
    ∀ u : ℝ, (153 / 200 : ℝ) ≤ u → u ≤ (613 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (14149 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (153 / 200 : ℝ) (613 / 800 : ℝ) (72159 / 15625 : ℝ) (4629739732489 / 1000000000000 : ℝ)
    (1943187 / 1250000 : ℝ) (7391 / 10000000000 : ℝ) (14149 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (153 / 200 : ℝ)) (72159 / 15625 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (613 / 800 : ℝ) (2151683 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (613 / 800 : ℝ))) h 2
    have he :
        (Real.exp (613 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (613 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (72159 / 15625 : ℝ) - (613 / 800 : ℝ) / 2) / 32)
      (1943187 / 1250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_613 :
    ∀ u : ℝ, (613 / 800 : ℝ) ≤ u → u ≤ (307 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (27451 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (613 / 800 : ℝ) (307 / 400 : ℝ) (578717 / 125000 : ℝ) (1160331832969 / 250000000000 : ℝ)
    (155628357 / 100000000 : ℝ) (1783 / 2500000000 : ℝ) (27451 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (613 / 800 : ℝ)) (578717 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (307 / 400 : ℝ) (1077187 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (307 / 400 : ℝ))) h 2
    have he :
        (Real.exp (307 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (307 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (578717 / 125000 : ℝ) - (307 / 400 : ℝ) / 2) / 32)
      (155628357 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_614 :
    ∀ u : ℝ, (307 / 400 : ℝ) ≤ u → u ≤ (123 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (106501 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (307 / 400 : ℝ) (123 / 160 : ℝ) (185653 / 40000 : ℝ) (4652946670761 / 1000000000000 : ℝ)
    (155802391 / 100000000 : ℝ) (6881 / 10000000000 : ℝ) (106501 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (307 / 400 : ℝ)) (185653 / 40000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (123 / 160 : ℝ) (2157069 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (123 / 160 : ℝ))) h 2
    have he :
        (Real.exp (123 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (123 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (185653 / 40000 : ℝ) - (123 / 160 : ℝ) / 2) / 32)
      (155802391 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_615 :
    ∀ u : ℝ, (123 / 160 : ℝ) ≤ u → u ≤ (77 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1033 / 1000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (123 / 160 : ℝ) (77 / 100 : ℝ) (2326471 / 500000 : ℝ) (4664593494289 / 1000000000000 : ℝ)
    (19497131 / 12500000 : ℝ) (6639 / 10000000000 : ℝ) (1033 / 1000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (123 / 160 : ℝ)) (2326471 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (77 / 100 : ℝ) (2159767 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (77 / 100 : ℝ))) h 2
    have he :
        (Real.exp (77 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (77 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2326471 / 500000 : ℝ) - (77 / 100 : ℝ) / 2) / 32)
      (19497131 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_616 :
    ∀ u : ℝ, (77 / 100 : ℝ) ≤ u → u ≤ (617 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (100171 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (77 / 100 : ℝ) (617 / 800 : ℝ) (4664589 / 1000000 : ℝ) (292266740689 / 62500000000 : ℝ)
    (3903809 / 2500000 : ℝ) (1601 / 2500000000 : ℝ) (100171 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (77 / 100 : ℝ)) (4664589 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (617 / 800 : ℝ) (540617 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (617 / 800 : ℝ))) h 2
    have he :
        (Real.exp (617 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (617 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4664589 / 1000000 : ℝ) - (617 / 800 : ℝ) / 2) / 32)
      (3903809 / 2500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_617 :
    ∀ u : ℝ, (617 / 800 : ℝ) ≤ u → u ≤ (309 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (24287 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (617 / 800 : ℝ) (309 / 400 : ℝ) (935253 / 200000 : ℝ) (4687974119929 / 1000000000000 : ℝ)
    (78164157 / 50000000 : ℝ) (3089 / 5000000000 : ℝ) (24287 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (617 / 800 : ℝ)) (935253 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (309 / 400 : ℝ) (2165173 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (309 / 400 : ℝ))) h 2
    have he :
        (Real.exp (309 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (309 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (935253 / 200000 : ℝ) - (309 / 400 : ℝ) / 2) / 32)
      (78164157 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_618 :
    ∀ u : ℝ, (309 / 400 : ℝ) ≤ u → u ≤ (619 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (471 / 500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (309 / 400 : ℝ) (619 / 800 : ℝ) (4687971 / 1000000 : ℝ) (4699708030161 / 1000000000000 : ℝ)
    (156504927 / 100000000 : ℝ) (5959 / 10000000000 : ℝ) (471 / 500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (309 / 400 : ℝ)) (4687971 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (619 / 800 : ℝ) (2167881 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (619 / 800 : ℝ))) h 2
    have he :
        (Real.exp (619 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (619 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4687971 / 1000000 : ℝ) - (619 / 800 : ℝ) / 2) / 32)
      (156504927 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_619 :
    ∀ u : ℝ, (619 / 800 : ℝ) ≤ u → u ≤ (31 / 40 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (9133 / 10000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (619 / 800 : ℝ) (31 / 40 : ℝ) (939941 / 200000 : ℝ) (4711473971649 / 1000000000000 : ℝ)
    (15668217 / 10000000 : ℝ) (5747 / 10000000000 : ℝ) (9133 / 10000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (619 / 800 : ℝ)) (939941 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (31 / 40 : ℝ) (2170593 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (31 / 40 : ℝ))) h 2
    have he :
        (Real.exp (31 / 40 : ℝ)) ^ 2 =
          Real.exp (2 * (31 / 40 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (939941 / 200000 : ℝ) - (31 / 40 : ℝ) / 2) / 32)
      (15668217 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_600
#print axioms hpThetaEnergyUpper_interval_619

end HodgeProofHP
