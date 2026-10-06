import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_780 :
    ∀ u : ℝ, (39 / 40 : ℝ) ≤ u → u ≤ (781 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (37 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (39 / 40 : ℝ) (781 / 800 : ℝ) (175717 / 25000 : ℝ) (440392831641 / 62500000000 : ℝ)
    (196292423 / 100000000 : ℝ) (1 / 2000000000 : ℝ) (37 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (39 / 40 : ℝ)) (175717 / 25000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (781 / 800 : ℝ) (663621 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (781 / 800 : ℝ))) h 2
    have he :
        (Real.exp (781 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (781 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (175717 / 25000 : ℝ) - (781 / 800 : ℝ) / 2) / 32)
      (196292423 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_781 :
    ∀ u : ℝ, (781 / 800 : ℝ) ≤ u → u ≤ (391 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (93 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (781 / 800 : ℝ) (391 / 400 : ℝ) (7046273 / 1000000 : ℝ) (441495131401 / 62500000000 : ℝ)
    (98313869 / 50000000 : ℝ) (1 / 2000000000 : ℝ) (93 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (781 / 800 : ℝ)) (7046273 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (391 / 400 : ℝ) (664451 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (391 / 400 : ℝ))) h 2
    have he :
        (Real.exp (391 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (391 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (7046273 / 1000000 : ℝ) - (391 / 400 : ℝ) / 2) / 32)
      (98313869 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_782 :
    ∀ u : ℝ, (391 / 400 : ℝ) ≤ u → u ≤ (783 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (149 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (391 / 400 : ℝ) (783 / 800 : ℝ) (7063911 / 1000000 : ℝ) (110650034881 / 15625000000 : ℝ)
    (39392899 / 20000000 : ℝ) (1 / 2500000000 : ℝ) (149 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (391 / 400 : ℝ)) (7063911 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (783 / 800 : ℝ) (332641 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (783 / 800 : ℝ))) h 2
    have he :
        (Real.exp (783 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (783 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (7063911 / 1000000 : ℝ) - (783 / 800 : ℝ) / 2) / 32)
      (39392899 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_783 :
    ∀ u : ℝ, (783 / 800 : ℝ) ≤ u → u ≤ (49 / 50 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (3 / 2000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (783 / 800 : ℝ) (49 / 50 : ℝ) (7081593 / 1000000 : ℝ) (7099331104849 / 1000000000000 : ℝ)
    (4932567 / 2500000 : ℝ) (1 / 2500000000 : ℝ) (3 / 2000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (783 / 800 : ℝ)) (7081593 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (49 / 50 : ℝ) (2664457 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (49 / 50 : ℝ))) h 2
    have he :
        (Real.exp (49 / 50 : ℝ)) ^ 2 =
          Real.exp (2 * (49 / 50 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (7081593 / 1000000 : ℝ) - (49 / 50 : ℝ) / 2) / 32)
      (4932567 / 2500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_784 :
    ∀ u : ℝ, (49 / 50 : ℝ) ≤ u → u ≤ (157 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (151 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (49 / 50 : ℝ) (157 / 160 : ℝ) (7099319 / 1000000 : ℝ) (7117098148521 / 1000000000000 : ℝ)
    (1976423 / 1000000 : ℝ) (1 / 2500000000 : ℝ) (151 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (49 / 50 : ℝ)) (7099319 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (157 / 160 : ℝ) (2667789 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (157 / 160 : ℝ))) h 2
    have he :
        (Real.exp (157 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (157 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (7099319 / 1000000 : ℝ) - (157 / 160 : ℝ) / 2) / 32)
      (1976423 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_785 :
    ∀ u : ℝ, (157 / 160 : ℝ) ≤ u → u ≤ (393 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (19 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (157 / 160 : ℝ) (393 / 400 : ℝ) (7117089 / 1000000 : ℝ) (1783728526969 / 250000000000 : ℝ)
    (98991679 / 50000000 : ℝ) (1 / 2500000000 : ℝ) (19 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (157 / 160 : ℝ)) (7117089 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (393 / 400 : ℝ) (1335563 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (393 / 400 : ℝ))) h 2
    have he :
        (Real.exp (393 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (393 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (7117089 / 1000000 : ℝ) - (393 / 400 : ℝ) / 2) / 32)
      (98991679 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_786 :
    ∀ u : ℝ, (393 / 400 : ℝ) ≤ u → u ≤ (787 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (153 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (393 / 400 : ℝ) (787 / 800 : ℝ) (891863 / 125000 : ℝ) (7152773734089 / 1000000000000 : ℝ)
    (99162941 / 50000000 : ℝ) (1 / 2500000000 : ℝ) (153 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (393 / 400 : ℝ)) (891863 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (787 / 800 : ℝ) (2674467 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (787 / 800 : ℝ))) h 2
    have he :
        (Real.exp (787 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (787 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (891863 / 125000 : ℝ) - (787 / 800 : ℝ) / 2) / 32)
      (99162941 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_787 :
    ∀ u : ℝ, (787 / 800 : ℝ) ≤ u → u ≤ (197 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (23 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (787 / 800 : ℝ) (197 / 200 : ℝ) (7152763 / 1000000 : ℝ) (448167319209 / 62500000000 : ℝ)
    (39733971 / 20000000 : ℝ) (3 / 10000000000 : ℝ) (23 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (787 / 800 : ℝ)) (7152763 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (197 / 200 : ℝ) (669453 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (197 / 200 : ℝ))) h 2
    have he :
        (Real.exp (197 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (197 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (7152763 / 1000000 : ℝ) - (197 / 200 : ℝ) / 2) / 32)
      (39733971 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_788 :
    ∀ u : ℝ, (197 / 200 : ℝ) ≤ u → u ≤ (789 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (29 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (197 / 200 : ℝ) (789 / 800 : ℝ) (1792667 / 250000 : ℝ) (1797157417561 / 250000000000 : ℝ)
    (49753831 / 25000000 : ℝ) (3 / 10000000000 : ℝ) (29 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (197 / 200 : ℝ)) (1792667 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (789 / 800 : ℝ) (1340581 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (789 / 800 : ℝ))) h 2
    have he :
        (Real.exp (789 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (789 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1792667 / 250000 : ℝ) - (789 / 800 : ℝ) / 2) / 32)
      (49753831 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_789 :
    ∀ u : ℝ, (789 / 800 : ℝ) ≤ u → u ≤ (79 / 80 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (29 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (789 / 800 : ℝ) (79 / 80 : ℝ) (7188617 / 1000000 : ℝ) (288264831409 / 40000000000 : ℝ)
    (199362253 / 100000000 : ℝ) (3 / 10000000000 : ℝ) (29 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (789 / 800 : ℝ)) (7188617 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (79 / 80 : ℝ) (536903 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (79 / 80 : ℝ))) h 2
    have he :
        (Real.exp (79 / 80 : ℝ)) ^ 2 =
          Real.exp (2 * (79 / 80 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (7188617 / 1000000 : ℝ) - (79 / 80 : ℝ) / 2) / 32)
      (199362253 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_790 :
    ∀ u : ℝ, (79 / 80 : ℝ) ≤ u → u ≤ (791 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (117 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (79 / 80 : ℝ) (791 / 800 : ℝ) (7206611 / 1000000 : ℝ) (7224661264129 / 1000000000000 : ℝ)
    (19971067 / 10000000 : ℝ) (3 / 10000000000 : ℝ) (117 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (79 / 80 : ℝ)) (7206611 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (791 / 800 : ℝ) (2687873 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (791 / 800 : ℝ))) h 2
    have he :
        (Real.exp (791 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (791 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (7206611 / 1000000 : ℝ) - (791 / 800 : ℝ) / 2) / 32)
      (19971067 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_791 :
    ∀ u : ℝ, (791 / 800 : ℝ) ≤ u → u ≤ (99 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (59 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (791 / 800 : ℝ) (99 / 100 : ℝ) (7224649 / 1000000 : ℝ) (289709833009 / 40000000000 : ℝ)
    (200060559 / 100000000 : ℝ) (3 / 10000000000 : ℝ) (59 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (791 / 800 : ℝ)) (7224649 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (99 / 100 : ℝ) (538247 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (99 / 100 : ℝ))) h 2
    have he :
        (Real.exp (99 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (99 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (7224649 / 1000000 : ℝ) - (99 / 100 : ℝ) / 2) / 32)
      (200060559 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_792 :
    ∀ u : ℝ, (99 / 100 : ℝ) ≤ u → u ≤ (793 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (59 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (99 / 100 : ℝ) (793 / 800 : ℝ) (3621367 / 500000 : ℝ) (7260874549201 / 1000000000000 : ℝ)
    (100205993 / 50000000 : ℝ) (3 / 10000000000 : ℝ) (59 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (99 / 100 : ℝ)) (3621367 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (793 / 800 : ℝ) (2694601 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (793 / 800 : ℝ))) h 2
    have he :
        (Real.exp (793 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (793 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3621367 / 500000 : ℝ) - (793 / 800 : ℝ) / 2) / 32)
      (100205993 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_793 :
    ∀ u : ℝ, (793 / 800 : ℝ) ≤ u → u ≤ (397 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (119 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (793 / 800 : ℝ) (397 / 400 : ℝ) (7260863 / 1000000 : ℝ) (7279047516841 / 1000000000000 : ℝ)
    (6273903 / 3125000 : ℝ) (3 / 10000000000 : ℝ) (119 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (793 / 800 : ℝ)) (7260863 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (397 / 400 : ℝ) (2697971 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (397 / 400 : ℝ))) h 2
    have he :
        (Real.exp (397 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (397 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (7260863 / 1000000 : ℝ) - (397 / 400 : ℝ) / 2) / 32)
      (6273903 / 3125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_794 :
    ∀ u : ℝ, (397 / 400 : ℝ) ≤ u → u ≤ (159 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1 / 1250000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (397 / 400 : ℝ) (159 / 160 : ℝ) (3639519 / 500000 : ℝ) (1824317552929 / 250000000000 : ℝ)
    (25139917 / 12500000 : ℝ) (1 / 5000000000 : ℝ) (1 / 1250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (397 / 400 : ℝ)) (3639519 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (159 / 160 : ℝ) (1350673 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (159 / 160 : ℝ))) h 2
    have he :
        (Real.exp (159 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (159 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3639519 / 500000 : ℝ) - (159 / 160 : ℝ) / 2) / 32)
      (25139917 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_795 :
    ∀ u : ℝ, (159 / 160 : ℝ) ≤ u → u ≤ (199 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1 / 1250000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (159 / 160 : ℝ) (199 / 200 : ℝ) (3648629 / 500000 : ℝ) (11704859721 / 1600000000 : ℝ)
    (201475291 / 100000000 : ℝ) (1 / 5000000000 : ℝ) (1 / 1250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (159 / 160 : ℝ)) (3648629 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (199 / 200 : ℝ) (108189 / 40000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (199 / 200 : ℝ))) h 2
    have he :
        (Real.exp (199 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (199 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3648629 / 500000 : ℝ) - (199 / 200 : ℝ) / 2) / 32)
      (201475291 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_796 :
    ∀ u : ℝ, (199 / 200 : ℝ) ≤ u → u ≤ (797 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (81 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (199 / 200 : ℝ) (797 / 800 : ℝ) (1828881 / 250000 : ℝ) (458365558729 / 62500000000 : ℝ)
    (201832787 / 100000000 : ℝ) (1 / 5000000000 : ℝ) (81 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (199 / 200 : ℝ)) (1828881 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (797 / 800 : ℝ) (677027 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (797 / 800 : ℝ))) h 2
    have he :
        (Real.exp (797 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (797 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1828881 / 250000 : ℝ) - (797 / 800 : ℝ) / 2) / 32)
      (201832787 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_797 :
    ∀ u : ℝ, (797 / 800 : ℝ) ≤ u → u ≤ (399 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (81 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (797 / 800 : ℝ) (399 / 400 : ℝ) (1466767 / 200000 : ℝ) (294088205401 / 40000000000 : ℝ)
    (202191811 / 100000000 : ℝ) (1 / 5000000000 : ℝ) (81 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (797 / 800 : ℝ)) (1466767 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (399 / 400 : ℝ) (542299 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (399 / 400 : ℝ))) h 2
    have he :
        (Real.exp (399 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (399 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1466767 / 200000 : ℝ) - (399 / 400 : ℝ) / 2) / 32)
      (202191811 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_798 :
    ∀ u : ℝ, (399 / 400 : ℝ) ≤ u → u ≤ (799 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (81 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (399 / 400 : ℝ) (799 / 800 : ℝ) (7352193 / 1000000 : ℝ) (7370611422769 / 1000000000000 : ℝ)
    (202552407 / 100000000 : ℝ) (1 / 5000000000 : ℝ) (81 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (399 / 400 : ℝ)) (7352193 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (799 / 800 : ℝ) (2714887 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (799 / 800 : ℝ))) h 2
    have he :
        (Real.exp (799 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (799 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (7352193 / 1000000 : ℝ) - (799 / 800 : ℝ) / 2) / 32)
      (202552407 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_799 :
    ∀ u : ℝ, (799 / 800 : ℝ) ≤ u → u ≤ (1 / 1 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (41 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (799 / 800 : ℝ) (1 / 1 : ℝ) (1842649 / 250000 : ℝ) (1847264257881 / 250000000000 : ℝ)
    (101457271 / 50000000 : ℝ) (1 / 5000000000 : ℝ) (41 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (799 / 800 : ℝ)) (1842649 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (1 / 1 : ℝ) (1359141 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (1 / 1 : ℝ))) h 2
    have he :
        (Real.exp (1 / 1 : ℝ)) ^ 2 =
          Real.exp (2 * (1 / 1 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1842649 / 250000 : ℝ) - (1 / 1 : ℝ) / 2) / 32)
      (101457271 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_780
#print axioms hpThetaEnergyUpper_interval_799

end HodgeProofHP
