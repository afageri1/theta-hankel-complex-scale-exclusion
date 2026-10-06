import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_60 :
    ∀ u : ℝ, (3 / 40 : ℝ) ≤ u → u ≤ (61 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (34668241 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (3 / 40 : ℝ) (61 / 800 : ℝ) (580917 / 500000 : ℝ) (1164743868289 / 1000000000000 : ℝ)
    (1399279 / 1250000 : ℝ) (270509357 / 10000000000 : ℝ) (34668241 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (3 / 40 : ℝ)) (580917 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (61 / 800 : ℝ) (1079233 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (61 / 800 : ℝ))) h 2
    have he :
        (Real.exp (61 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (61 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (580917 / 500000 : ℝ) - (61 / 800 : ℝ) / 2) / 32)
      (1399279 / 1250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_61 :
    ∀ u : ℝ, (61 / 800 : ℝ) ≤ u → u ≤ (31 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (173030093 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (61 / 800 : ℝ) (31 / 400 : ℝ) (582371 / 500000 : ℝ) (1167659619889 / 1000000000000 : ℝ)
    (1399651 / 1250000 : ℝ) (134109067 / 5000000000 : ℝ) (173030093 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (61 / 800 : ℝ)) (582371 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (31 / 400 : ℝ) (1080583 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (31 / 400 : ℝ))) h 2
    have he :
        (Real.exp (31 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (31 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (582371 / 500000 : ℝ) - (31 / 400 : ℝ) / 2) / 32)
      (1399651 / 1250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_62 :
    ∀ u : ℝ, (31 / 400 : ℝ) ≤ u → u ≤ (63 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (34542757 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (31 / 400 : ℝ) (63 / 800 : ℝ) (1167657 / 1000000 : ℝ) (292645295089 / 250000000000 : ℝ)
    (4480077 / 4000000 : ℝ) (13297023 / 500000000 : ℝ) (34542757 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (31 / 400 : ℝ)) (1167657 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (63 / 800 : ℝ) (540967 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (63 / 800 : ℝ))) h 2
    have he :
        (Real.exp (63 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (63 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1167657 / 1000000 : ℝ) - (63 / 800 : ℝ) / 2) / 32)
      (4480077 / 4000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_63 :
    ∀ u : ℝ, (63 / 800 : ℝ) ≤ u → u ≤ (2 / 25 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (17239387 / 10000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (63 / 800 : ℝ) (2 / 25 : ℝ) (58529 / 50000 : ℝ) (18336138921 / 15625000000 : ℝ)
    (22406373 / 20000000 : ℝ) (65918893 / 2500000000 : ℝ) (17239387 / 10000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (63 / 800 : ℝ)) (58529 / 50000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (2 / 25 : ℝ) (135411 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (2 / 25 : ℝ))) h 2
    have he :
        (Real.exp (2 / 25 : ℝ)) ^ 2 =
          Real.exp (2 * (2 / 25 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (58529 / 50000 : ℝ) - (2 / 25 : ℝ) / 2) / 32)
      (22406373 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_64 :
    ∀ u : ℝ, (2 / 25 : ℝ) ≤ u → u ≤ (13 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (172068787 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (2 / 25 : ℝ) (13 / 160 : ℝ) (117351 / 100000 : ℝ) (1176450437449 / 1000000000000 : ℝ)
    (112061891 / 100000000 : ℝ) (5228483 / 200000000 : ℝ) (172068787 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (2 / 25 : ℝ)) (117351 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (13 / 160 : ℝ) (1084643 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (13 / 160 : ℝ))) h 2
    have he :
        (Real.exp (13 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (13 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (117351 / 100000 : ℝ) - (13 / 160 : ℝ) / 2) / 32)
      (112061891 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_65 :
    ∀ u : ℝ, (13 / 160 : ℝ) ≤ u → u ≤ (33 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (34347599 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (13 / 160 : ℝ) (33 / 400 : ℝ) (18382 / 15625 : ℝ) (1179393828001 / 1000000000000 : ℝ)
    (112092013 / 100000000 : ℝ) (51837089 / 2000000000 : ℝ) (34347599 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (13 / 160 : ℝ)) (18382 / 15625 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (33 / 400 : ℝ) (1085999 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (33 / 400 : ℝ))) h 2
    have he :
        (Real.exp (33 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (33 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (18382 / 15625 : ℝ) - (33 / 400 : ℝ) / 2) / 32)
      (112092013 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_66 :
    ∀ u : ℝ, (33 / 400 : ℝ) ≤ u → u ≤ (67 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (85702143 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (33 / 400 : ℝ) (67 / 800 : ℝ) (1179393 / 1000000 : ℝ) (295586855041 / 250000000000 : ℝ)
    (5606111 / 5000000 : ℝ) (256960271 / 10000000000 : ℝ) (85702143 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (33 / 400 : ℝ)) (1179393 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (67 / 800 : ℝ) (543679 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (67 / 800 : ℝ))) h 2
    have he :
        (Real.exp (67 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (67 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1179393 / 1000000 : ℝ) - (67 / 800 : ℝ) / 2) / 32)
      (5606111 / 5000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_67 :
    ∀ u : ℝ, (67 / 800 : ℝ) ≤ u → u ≤ (17 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (171065583 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (67 / 800 : ℝ) (17 / 200 : ℝ) (236469 / 200000 : ℝ) (296326720881 / 250000000000 : ℝ)
    (1752383 / 1562500 : ℝ) (254748613 / 10000000000 : ℝ) (171065583 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (67 / 800 : ℝ)) (236469 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (17 / 200 : ℝ) (544359 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (17 / 200 : ℝ))) h 2
    have he :
        (Real.exp (17 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (17 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (236469 / 200000 : ℝ) - (17 / 200 : ℝ) / 2) / 32)
      (1752383 / 1562500 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_68 :
    ∀ u : ℝ, (17 / 200 : ℝ) ≤ u → u ≤ (69 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (85360967 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (17 / 200 : ℝ) (69 / 800 : ℝ) (148163 / 125000 : ℝ) (1188272226241 / 1000000000000 : ℝ)
    (112182889 / 100000000 : ℝ) (126275229 / 5000000000 : ℝ) (85360967 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (17 / 200 : ℝ)) (148163 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (69 / 800 : ℝ) (1090079 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (69 / 800 : ℝ))) h 2
    have he :
        (Real.exp (69 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (69 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (148163 / 125000 : ℝ) - (69 / 800 : ℝ) / 2) / 32)
      (112182889 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_69 :
    ∀ u : ℝ, (69 / 800 : ℝ) ≤ u → u ≤ (7 / 80 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (8518739 / 5000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (69 / 800 : ℝ) (7 / 80 : ℝ) (1188271 / 1000000 : ℝ) (1191247822249 / 1000000000000 : ℝ)
    (112213363 / 100000000 : ℝ) (250364931 / 10000000000 : ℝ) (8518739 / 5000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (69 / 800 : ℝ)) (1188271 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (7 / 80 : ℝ) (1091443 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (7 / 80 : ℝ))) h 2
    have he :
        (Real.exp (7 / 80 : ℝ)) ^ 2 =
          Real.exp (2 * (7 / 80 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1188271 / 1000000 : ℝ) - (7 / 80 : ℝ) / 2) / 32)
      (112213363 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_70 :
    ∀ u : ℝ, (7 / 80 : ℝ) ≤ u → u ≤ (71 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (170022133 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (7 / 80 : ℝ) (71 / 800 : ℝ) (595623 / 500000 : ℝ) (18659833201 / 15625000000 : ℝ)
    (112243933 / 100000000 : ℝ) (248192111 / 10000000000 : ℝ) (170022133 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (7 / 80 : ℝ)) (595623 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (71 / 800 : ℝ) (136601 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (71 / 800 : ℝ))) h 2
    have he :
        (Real.exp (71 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (71 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (595623 / 500000 : ℝ) - (71 / 800 : ℝ) / 2) / 32)
      (112243933 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_71 :
    ∀ u : ℝ, (71 / 800 : ℝ) ≤ u → u ≤ (9 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (10604103 / 6250000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (71 / 800 : ℝ) (9 / 100 : ℝ) (298557 / 250000 : ℝ) (1915550289 / 1600000000 : ℝ)
    (112274589 / 100000000 : ℝ) (246032701 / 10000000000 : ℝ) (10604103 / 6250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (71 / 800 : ℝ)) (298557 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (9 / 100 : ℝ) (43767 / 40000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (9 / 100 : ℝ))) h 2
    have he :
        (Real.exp (9 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (9 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (298557 / 250000 : ℝ) - (9 / 100 : ℝ) / 2) / 32)
      (112274589 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_72 :
    ∀ u : ℝ, (9 / 100 : ℝ) ≤ u → u ≤ (73 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (169304387 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (9 / 100 : ℝ) (73 / 800 : ℝ) (1197217 / 1000000 : ℝ) (1200214464849 / 1000000000000 : ℝ)
    (11230533 / 10000000 : ℝ) (48777351 / 2000000000 : ℝ) (169304387 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (9 / 100 : ℝ)) (1197217 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (73 / 800 : ℝ) (1095543 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (73 / 800 : ℝ))) h 2
    have he :
        (Real.exp (73 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (73 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1197217 / 1000000 : ℝ) - (73 / 800 : ℝ) / 2) / 32)
      (11230533 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_73 :
    ∀ u : ℝ, (73 / 800 : ℝ) ≤ u → u ≤ (37 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (5279369 / 3125000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (73 / 800 : ℝ) (37 / 400 : ℝ) (600107 / 500000 : ℝ) (300805080849 / 250000000000 : ℝ)
    (112336167 / 100000000 : ℝ) (120876747 / 5000000000 : ℝ) (5279369 / 3125000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (73 / 800 : ℝ)) (600107 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (37 / 400 : ℝ) (548457 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (37 / 400 : ℝ))) h 2
    have he :
        (Real.exp (37 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (37 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (600107 / 500000 : ℝ) - (37 / 400 : ℝ) / 2) / 32)
      (112336167 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_74 :
    ∀ u : ℝ, (37 / 400 : ℝ) ≤ u → u ≤ (3 / 32 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (33714097 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (37 / 400 : ℝ) (3 / 32 : ℝ) (601609 / 500000 : ℝ) (301558034449 / 250000000000 : ℝ)
    (11236709 / 10000000 : ℝ) (239633601 / 10000000000 : ℝ) (33714097 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (37 / 400 : ℝ)) (601609 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (3 / 32 : ℝ) (549143 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (3 / 32 : ℝ))) h 2
    have he :
        (Real.exp (3 / 32 : ℝ)) ^ 2 =
          Real.exp (2 * (3 / 32 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (601609 / 500000 : ℝ) - (3 / 32 : ℝ) / 2) / 32)
      (11236709 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_75 :
    ∀ u : ℝ, (3 / 32 : ℝ) ≤ u → u ≤ (19 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (3363917 / 2000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (3 / 32 : ℝ) (19 / 200 : ℝ) (120623 / 100000 : ℝ) (1209249916281 / 1000000000000 : ℝ)
    (11239811 / 10000000 : ℝ) (237526313 / 10000000000 : ℝ) (3363917 / 2000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (3 / 32 : ℝ)) (120623 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (19 / 200 : ℝ) (1099659 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (19 / 200 : ℝ))) h 2
    have he :
        (Real.exp (19 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (19 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (120623 / 100000 : ℝ) - (19 / 200 : ℝ) / 2) / 32)
      (11239811 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_76 :
    ∀ u : ℝ, (19 / 200 : ℝ) ≤ u → u ≤ (77 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (83909287 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (19 / 200 : ℝ) (77 / 800 : ℝ) (1209249 / 1000000 : ℝ) (48491122849 / 40000000000 : ℝ)
    (3513413 / 3125000 : ℝ) (14714523 / 625000000 : ℝ) (83909287 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (19 / 200 : ℝ)) (1209249 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (77 / 800 : ℝ) (220207 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (77 / 800 : ℝ))) h 2
    have he :
        (Real.exp (77 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (77 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1209249 / 1000000 : ℝ) - (77 / 800 : ℝ) / 2) / 32)
      (3513413 / 3125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_77 :
    ∀ u : ℝ, (77 / 800 : ℝ) ≤ u → u ≤ (39 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (167436073 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (77 / 800 : ℝ) (39 / 400 : ℝ) (303069 / 250000 : ℝ) (75957013609 / 62500000000 : ℝ)
    (112460419 / 100000000 : ℝ) (58337753 / 2500000000 : ℝ) (167436073 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (77 / 800 : ℝ)) (303069 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (39 / 400 : ℝ) (275603 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (39 / 400 : ℝ))) h 2
    have he :
        (Real.exp (39 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (39 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (303069 / 250000 : ℝ) - (39 / 400 : ℝ) / 2) / 32)
      (112460419 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_78 :
    ∀ u : ℝ, (39 / 400 : ℝ) ≤ u → u ≤ (79 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (3341001 / 2000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (39 / 400 : ℝ) (79 / 800 : ℝ) (121531 / 100000 : ℝ) (1218354571681 / 1000000000000 : ℝ)
    (112491707 / 100000000 : ℝ) (115641517 / 5000000000 : ℝ) (3341001 / 2000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (39 / 400 : ℝ)) (121531 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (79 / 800 : ℝ) (1103791 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (79 / 800 : ℝ))) h 2
    have he :
        (Real.exp (79 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (79 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (121531 / 100000 : ℝ) - (79 / 800 : ℝ) / 2) / 32)
      (112491707 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_79 :
    ∀ u : ℝ, (79 / 800 : ℝ) ≤ u → u ≤ (1 / 10 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (41664561 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (79 / 800 : ℝ) (1 / 10 : ℝ) (1218353 / 1000000 : ℝ) (1221402939241 / 1000000000000 : ℝ)
    (3516347 / 3125000 : ℝ) (45845369 / 2000000000 : ℝ) (41664561 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (79 / 800 : ℝ)) (1218353 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (1 / 10 : ℝ) (1105171 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (1 / 10 : ℝ))) h 2
    have he :
        (Real.exp (1 / 10 : ℝ)) ^ 2 =
          Real.exp (2 * (1 / 10 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1218353 / 1000000 : ℝ) - (1 / 10 : ℝ) / 2) / 32)
      (3516347 / 3125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_60
#print axioms hpThetaEnergyUpper_interval_79

end HodgeProofHP
