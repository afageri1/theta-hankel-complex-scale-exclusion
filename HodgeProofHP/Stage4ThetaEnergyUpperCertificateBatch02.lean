import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_40 :
    ∀ u : ℝ, (1 / 20 : ℝ) ≤ u → u ≤ (41 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (89281239 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (1 / 20 : ℝ) (41 / 800 : ℝ) (110517 / 100000 : ℝ) (1107939392569 / 1000000000000 : ℝ)
    (27841281 / 25000000 : ℝ) (319172483 / 10000000000 : ℝ) (89281239 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (1 / 20 : ℝ)) (110517 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (41 / 800 : ℝ) (1052587 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (41 / 800 : ℝ))) h 2
    have he :
        (Real.exp (41 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (41 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (110517 / 100000 : ℝ) - (41 / 800 : ℝ) / 2) / 32)
      (27841281 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_41 :
    ∀ u : ℝ, (41 / 800 : ℝ) ≤ u → u ≤ (21 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (89173661 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (41 / 800 : ℝ) (21 / 400 : ℝ) (1107937 / 1000000 : ℝ) (1110711533409 / 1000000000000 : ℝ)
    (111393189 / 100000000 : ℝ) (316609257 / 10000000000 : ℝ) (89173661 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (41 / 800 : ℝ)) (1107937 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (21 / 400 : ℝ) (1053903 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (21 / 400 : ℝ))) h 2
    have he :
        (Real.exp (21 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (21 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1107937 / 1000000 : ℝ) - (21 / 400 : ℝ) / 2) / 32)
      (111393189 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_42 :
    ∀ u : ℝ, (21 / 400 : ℝ) ≤ u → u ≤ (43 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (8906407 / 5000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (21 / 400 : ℝ) (43 / 800 : ℝ) (111071 / 100000 : ℝ) (1113491358841 / 1000000000000 : ℝ)
    (111421327 / 100000000 : ℝ) (31406067 / 1000000000 : ℝ) (8906407 / 5000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (21 / 400 : ℝ)) (111071 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (43 / 800 : ℝ) (1055221 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (43 / 800 : ℝ))) h 2
    have he :
        (Real.exp (43 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (43 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (111071 / 100000 : ℝ) - (43 / 800 : ℝ) / 2) / 32)
      (111421327 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_43 :
    ∀ u : ℝ, (43 / 800 : ℝ) ≤ u → u ≤ (11 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (88952137 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (43 / 800 : ℝ) (11 / 200 : ℝ) (111349 / 100000 : ℝ) (1116278884681 / 1000000000000 : ℝ)
    (111449549 / 100000000 : ℝ) (7788143 / 250000000 : ℝ) (88952137 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (43 / 800 : ℝ)) (111349 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (11 / 200 : ℝ) (1056541 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (11 / 200 : ℝ))) h 2
    have he :
        (Real.exp (11 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (11 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (111349 / 100000 : ℝ) - (11 / 200 : ℝ) / 2) / 32)
      (111449549 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_44 :
    ∀ u : ℝ, (11 / 200 : ℝ) ≤ u → u ≤ (9 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (88837561 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (11 / 200 : ℝ) (9 / 160 : ℝ) (558139 / 500000 : ℝ) (1119074126769 / 1000000000000 : ℝ)
    (22295573 / 20000000 : ℝ) (38625441 / 1250000000 : ℝ) (88837561 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (11 / 200 : ℝ)) (558139 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (9 / 160 : ℝ) (1057863 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (9 / 160 : ℝ))) h 2
    have he :
        (Real.exp (9 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (9 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (558139 / 500000 : ℝ) - (9 / 160 : ℝ) / 2) / 32)
      (22295573 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_45 :
    ∀ u : ℝ, (9 / 160 : ℝ) ≤ u → u ≤ (23 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (177440807 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (9 / 160 : ℝ) (23 / 400 : ℝ) (34971 / 31250 : ℝ) (280468745649 / 250000000000 : ℝ)
    (22301251 / 20000000 : ℝ) (306495879 / 10000000000 : ℝ) (177440807 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (9 / 160 : ℝ)) (34971 / 31250 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (23 / 400 : ℝ) (529593 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (23 / 400 : ℝ))) h 2
    have he :
        (Real.exp (23 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (23 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (34971 / 31250 : ℝ) - (23 / 400 : ℝ) / 2) / 32)
      (22301251 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_46 :
    ∀ u : ℝ, (23 / 400 : ℝ) ≤ u → u ≤ (47 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (44300487 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (23 / 400 : ℝ) (47 / 800 : ℝ) (1121873 / 1000000 : ℝ) (1124683581121 / 1000000000000 : ℝ)
    (13941841 / 12500000 : ℝ) (76000493 / 2500000000 : ℝ) (44300487 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (23 / 400 : ℝ)) (1121873 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (47 / 800 : ℝ) (1060511 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (47 / 800 : ℝ))) h 2
    have he :
        (Real.exp (47 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (47 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1121873 / 1000000 : ℝ) - (47 / 800 : ℝ) / 2) / 32)
      (13941841 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_47 :
    ∀ u : ℝ, (47 / 800 : ℝ) ≤ u → u ≤ (3 / 50 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (44239343 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (47 / 800 : ℝ) (3 / 50 : ℝ) (1124681 / 1000000 : ℝ) (1127497814569 / 1000000000000 : ℝ)
    (22312657 / 20000000 : ℝ) (301521721 / 10000000000 : ℝ) (44239343 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (47 / 800 : ℝ)) (1124681 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (3 / 50 : ℝ) (1061837 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (3 / 50 : ℝ))) h 2
    have he :
        (Real.exp (3 / 50 : ℝ)) ^ 2 =
          Real.exp (2 * (3 / 50 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1124681 / 1000000 : ℝ) - (3 / 50 : ℝ) / 2) / 32)
      (22312657 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_48 :
    ∀ u : ℝ, (3 / 50 : ℝ) ≤ u → u ≤ (49 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (35341653 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (3 / 50 : ℝ) (49 / 800 : ℝ) (140937 / 125000 : ℝ) (45212792689 / 40000000000 : ℝ)
    (55795963 / 50000000 : ℝ) (29905513 / 1000000000 : ℝ) (35341653 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (3 / 50 : ℝ)) (140937 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (49 / 800 : ℝ) (212633 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (49 / 800 : ℝ))) h 2
    have he :
        (Real.exp (49 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (49 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (140937 / 125000 : ℝ) - (49 / 800 : ℝ) / 2) / 32)
      (55795963 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_49 :
    ∀ u : ℝ, (49 / 800 : ℝ) ≤ u → u ≤ (1 / 16 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (44113509 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (49 / 800 : ℝ) (1 / 16 : ℝ) (1130319 / 1000000 : ℝ) (45325984201 / 40000000000 : ℝ)
    (111620661 / 100000000 : ℝ) (74150337 / 2500000000 : ℝ) (44113509 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (49 / 800 : ℝ)) (1130319 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (1 / 16 : ℝ) (212899 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (1 / 16 : ℝ))) h 2
    have he :
        (Real.exp (1 / 16 : ℝ)) ^ 2 =
          Real.exp (2 * (1 / 16 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1130319 / 1000000 : ℝ) - (1 / 16 : ℝ) / 2) / 32)
      (111620661 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_50 :
    ∀ u : ℝ, (1 / 16 : ℝ) ≤ u → u ≤ (51 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (176194819 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (1 / 16 : ℝ) (51 / 800 : ℝ) (283287 / 250000 : ℝ) (283996265569 / 250000000000 : ℝ)
    (11164947 / 10000000 : ℝ) (58832417 / 2000000000 : ℝ) (176194819 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (1 / 16 : ℝ)) (283287 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (51 / 800 : ℝ) (532913 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (51 / 800 : ℝ))) h 2
    have he :
        (Real.exp (51 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (51 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (283287 / 250000 : ℝ) - (51 / 800 : ℝ) / 2) / 32)
      (11164947 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_51 :
    ∀ u : ℝ, (51 / 800 : ℝ) ≤ u → u ≤ (13 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (87966121 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (51 / 800 : ℝ) (13 / 200 : ℝ) (70999 / 62500 : ℝ) (711769041 / 625000000 : ℝ)
    (27919591 / 25000000 : ℝ) (145868199 / 5000000000 : ℝ) (87966121 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (51 / 800 : ℝ)) (70999 / 62500 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (13 / 200 : ℝ) (26679 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (13 / 200 : ℝ))) h 2
    have he :
        (Real.exp (13 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (13 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (70999 / 62500 : ℝ) - (13 / 200 : ℝ) / 2) / 32)
      (27919591 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_52 :
    ∀ u : ℝ, (13 / 200 : ℝ) ≤ u → u ≤ (53 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (175662387 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (13 / 200 : ℝ) (53 / 800 : ℝ) (284707 / 250000 : ℝ) (285419857009 / 250000000000 : ℝ)
    (13963419 / 12500000 : ℝ) (289323543 / 10000000000 : ℝ) (175662387 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (13 / 200 : ℝ)) (284707 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (53 / 800 : ℝ) (534247 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (53 / 800 : ℝ))) h 2
    have he :
        (Real.exp (53 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (53 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (284707 / 250000 : ℝ) - (53 / 800 : ℝ) / 2) / 32)
      (13963419 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_53 :
    ∀ u : ℝ, (53 / 800 : ℝ) ≤ u → u ≤ (27 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (175389233 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (53 / 800 : ℝ) (27 / 400 : ℝ) (1141679 / 1000000 : ℝ) (1144538368561 / 1000000000000 : ℝ)
    (4469457 / 4000000 : ℝ) (286924277 / 10000000000 : ℝ) (175389233 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (53 / 800 : ℝ)) (1141679 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (27 / 400 : ℝ) (1069831 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (27 / 400 : ℝ))) h 2
    have he :
        (Real.exp (27 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (27 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1141679 / 1000000 : ℝ) - (27 / 400 : ℝ) / 2) / 32)
      (4469457 / 4000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_54 :
    ∀ u : ℝ, (27 / 400 : ℝ) ≤ u → u ≤ (11 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (87555639 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (27 / 400 : ℝ) (11 / 160 : ℝ) (143067 / 125000 : ℝ) (1147403026561 / 1000000000000 : ℝ)
    (111765571 / 100000000 : ℝ) (284539577 / 10000000000 : ℝ) (87555639 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (27 / 400 : ℝ)) (143067 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (11 / 160 : ℝ) (1071169 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (11 / 160 : ℝ))) h 2
    have he :
        (Real.exp (11 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (11 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (143067 / 125000 : ℝ) - (11 / 160 : ℝ) / 2) / 32)
      (111765571 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_55 :
    ∀ u : ℝ, (11 / 160 : ℝ) ≤ u → u ≤ (7 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (87414177 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (11 / 160 : ℝ) (7 / 100 : ℝ) (1147401 / 1000000 : ℝ) (1150275555081 / 1000000000000 : ℝ)
    (27948703 / 25000000 : ℝ) (141083819 / 5000000000 : ℝ) (87414177 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (11 / 160 : ℝ)) (1147401 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (7 / 100 : ℝ) (1072509 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (7 / 100 : ℝ))) h 2
    have he :
        (Real.exp (7 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (7 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1147401 / 1000000 : ℝ) - (7 / 100 : ℝ) / 2) / 32)
      (27948703 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_56 :
    ∀ u : ℝ, (7 / 100 : ℝ) ≤ u → u ≤ (57 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (174539997 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (7 / 100 : ℝ) (57 / 800 : ℝ) (1150273 / 1000000 : ℝ) (461261529 / 400000000 : ℝ)
    (55912069 / 50000000 : ℝ) (279809277 / 10000000000 : ℝ) (174539997 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (7 / 100 : ℝ)) (1150273 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (57 / 800 : ℝ) (21477 / 20000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (57 / 800 : ℝ))) h 2
    have he :
        (Real.exp (57 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (57 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1150273 / 1000000 : ℝ) - (57 / 800 : ℝ) / 2) / 32)
      (55912069 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_57 :
    ∀ u : ℝ, (57 / 800 : ℝ) ≤ u → u ≤ (29 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (43561687 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (57 / 800 : ℝ) (29 / 400 : ℝ) (1153153 / 1000000 : ℝ) (1156039987249 / 1000000000000 : ℝ)
    (111853559 / 100000000 : ℝ) (138731849 / 5000000000 : ℝ) (43561687 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (57 / 800 : ℝ)) (1153153 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (29 / 400 : ℝ) (1075193 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (29 / 400 : ℝ))) h 2
    have he :
        (Real.exp (29 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (29 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1153153 / 1000000 : ℝ) - (29 / 400 : ℝ) / 2) / 32)
      (111853559 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_58 :
    ∀ u : ℝ, (29 / 400 : ℝ) ≤ u → u ≤ (59 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (34789979 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (29 / 400 : ℝ) (59 / 800 : ℝ) (1156039 / 1000000 : ℝ) (289733516361 / 250000000000 : ℝ)
    (55941527 / 50000000 : ℝ) (275132567 / 10000000000 : ℝ) (34789979 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (29 / 400 : ℝ)) (1156039 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (59 / 800 : ℝ) (538269 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (59 / 800 : ℝ))) h 2
    have he :
        (Real.exp (59 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (59 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1156039 / 1000000 : ℝ) - (59 / 800 : ℝ) / 2) / 32)
      (55941527 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_59 :
    ∀ u : ℝ, (59 / 800 : ℝ) ≤ u → u ≤ (3 / 40 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (86824107 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (59 / 800 : ℝ) (3 / 40 : ℝ) (1158933 / 1000000 : ℝ) (46473442929 / 40000000000 : ℝ)
    (27978161 / 25000000 : ℝ) (272814217 / 10000000000 : ℝ) (86824107 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (59 / 800 : ℝ)) (1158933 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (3 / 40 : ℝ) (215577 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (3 / 40 : ℝ))) h 2
    have he :
        (Real.exp (3 / 40 : ℝ)) ^ 2 =
          Real.exp (2 * (3 / 40 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1158933 / 1000000 : ℝ) - (3 / 40 : ℝ) / 2) / 32)
      (27978161 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_40
#print axioms hpThetaEnergyUpper_interval_59

end HodgeProofHP
