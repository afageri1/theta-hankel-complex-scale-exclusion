import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_680 :
    ∀ u : ℝ, (17 / 20 : ℝ) ≤ u → u ≤ (681 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (5749 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (17 / 20 : ℝ) (681 / 800 : ℝ) (1094789 / 200000 : ℝ) (1371913236369 / 250000000000 : ℝ)
    (42212057 / 25000000 : ℝ) (21 / 400000000 : ℝ) (5749 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (17 / 20 : ℝ)) (1094789 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (681 / 800 : ℝ) (1171287 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (681 / 800 : ℝ))) h 2
    have he :
        (Real.exp (681 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (681 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1094789 / 200000 : ℝ) - (681 / 800 : ℝ) / 2) / 32)
      (42212057 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_681 :
    ∀ u : ℝ, (681 / 800 : ℝ) ≤ u → u ≤ (341 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1387 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (681 / 800 : ℝ) (341 / 400 : ℝ) (5487647 / 1000000 : ℝ) (5372450209 / 976562500 : ℝ)
    (169072097 / 100000000 : ℝ) (63 / 1250000000 : ℝ) (1387 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (681 / 800 : ℝ)) (5487647 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (341 / 400 : ℝ) (73297 / 31250 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (341 / 400 : ℝ))) h 2
    have he :
        (Real.exp (341 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (341 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (5487647 / 1000000 : ℝ) - (341 / 400 : ℝ) / 2) / 32)
      (169072097 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_682 :
    ∀ u : ℝ, (341 / 400 : ℝ) ≤ u → u ≤ (683 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (10689 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (341 / 400 : ℝ) (683 / 800 : ℝ) (687673 / 125000 : ℝ) (5515156342969 / 1000000000000 : ℝ)
    (169296843 / 100000000 : ℝ) (483 / 10000000000 : ℝ) (10689 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (341 / 400 : ℝ)) (687673 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (683 / 800 : ℝ) (2348437 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (683 / 800 : ℝ))) h 2
    have he :
        (Real.exp (683 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (683 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (687673 / 125000 : ℝ) - (683 / 800 : ℝ) / 2) / 32)
      (169296843 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_683 :
    ∀ u : ℝ, (683 / 800 : ℝ) ≤ u → u ≤ (171 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (10301 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (683 / 800 : ℝ) (171 / 200 : ℝ) (2757577 / 500000 : ℝ) (353853721 / 64000000 : ℝ)
    (84761219 / 50000000 : ℝ) (463 / 10000000000 : ℝ) (10301 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (683 / 800 : ℝ)) (2757577 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (171 / 200 : ℝ) (18811 / 8000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (171 / 200 : ℝ))) h 2
    have he :
        (Real.exp (171 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (171 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2757577 / 500000 : ℝ) - (171 / 200 : ℝ) / 2) / 32)
      (84761219 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_684 :
    ∀ u : ℝ, (171 / 200 : ℝ) ≤ u → u ≤ (137 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (9907 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (171 / 200 : ℝ) (137 / 160 : ℝ) (5528959 / 1000000 : ℝ) (346425239241 / 62500000000 : ℝ)
    (42437229 / 25000000 : ℝ) (443 / 10000000000 : ℝ) (9907 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (171 / 200 : ℝ)) (5528959 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (137 / 160 : ℝ) (588579 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (137 / 160 : ℝ))) h 2
    have he :
        (Real.exp (137 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (137 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (5528959 / 1000000 : ℝ) - (137 / 160 : ℝ) / 2) / 32)
      (42437229 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_685 :
    ∀ u : ℝ, (137 / 160 : ℝ) ≤ u → u ≤ (343 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1911 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (137 / 160 : ℝ) (343 / 400 : ℝ) (5542799 / 1000000 : ℝ) (5556679422121 / 1000000000000 : ℝ)
    (4249407 / 2500000 : ℝ) (17 / 400000000 : ℝ) (1911 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (137 / 160 : ℝ)) (5542799 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (343 / 400 : ℝ) (2357261 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (343 / 400 : ℝ))) h 2
    have he :
        (Real.exp (343 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (343 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (5542799 / 1000000 : ℝ) - (343 / 400 : ℝ) / 2) / 32)
      (4249407 / 2500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_686 :
    ∀ u : ℝ, (343 / 400 : ℝ) ≤ u → u ≤ (687 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (4599 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (343 / 400 : ℝ) (687 / 800 : ℝ) (5556673 / 1000000 : ℝ) (5570586523681 / 1000000000000 : ℝ)
    (170204517 / 100000000 : ℝ) (407 / 10000000000 : ℝ) (4599 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (343 / 400 : ℝ)) (5556673 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (687 / 800 : ℝ) (2360209 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (687 / 800 : ℝ))) h 2
    have he :
        (Real.exp (687 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (687 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (5556673 / 1000000 : ℝ) - (687 / 800 : ℝ) / 2) / 32)
      (170204517 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_687 :
    ∀ u : ℝ, (687 / 800 : ℝ) ≤ u → u ≤ (43 / 50 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (443 / 5000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (687 / 800 : ℝ) (43 / 50 : ℝ) (2785291 / 500000 : ℝ) (5584529911921 / 1000000000000 : ℝ)
    (34086729 / 20000000 : ℝ) (39 / 1000000000 : ℝ) (443 / 5000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (687 / 800 : ℝ)) (2785291 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (43 / 50 : ℝ) (2363161 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (43 / 50 : ℝ))) h 2
    have he :
        (Real.exp (43 / 50 : ℝ)) ^ 2 =
          Real.exp (2 * (43 / 50 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2785291 / 500000 : ℝ) - (43 / 50 : ℝ) / 2) / 32)
      (34086729 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_688 :
    ∀ u : ℝ, (43 / 50 : ℝ) ≤ u → u ≤ (689 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (4259 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (43 / 50 : ℝ) (689 / 800 : ℝ) (2792263 / 500000 : ℝ) (5598509657689 / 1000000000000 : ℝ)
    (42665917 / 25000000 : ℝ) (373 / 10000000000 : ℝ) (4259 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (43 / 50 : ℝ)) (2792263 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (689 / 800 : ℝ) (2366117 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (689 / 800 : ℝ))) h 2
    have he :
        (Real.exp (689 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (689 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2792263 / 500000 : ℝ) - (689 / 800 : ℝ) / 2) / 32)
      (42665917 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_689 :
    ∀ u : ℝ, (689 / 800 : ℝ) ≤ u → u ≤ (69 / 80 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (8219 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (689 / 800 : ℝ) (69 / 80 : ℝ) (1119701 / 200000 : ℝ) (350782568361 / 62500000000 : ℝ)
    (42723647 / 25000000 : ℝ) (179 / 5000000000 : ℝ) (8219 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (689 / 800 : ℝ)) (1119701 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (69 / 80 : ℝ) (592269 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (69 / 80 : ℝ))) h 2
    have he :
        (Real.exp (69 / 80 : ℝ)) ^ 2 =
          Real.exp (2 * (69 / 80 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1119701 / 200000 : ℝ) - (69 / 80 : ℝ) / 2) / 32)
      (42723647 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_690 :
    ∀ u : ℝ, (69 / 80 : ℝ) ≤ u → u ≤ (691 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (7893 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (69 / 80 : ℝ) (691 / 800 : ℝ) (5612519 / 1000000 : ℝ) (3516608601 / 625000000 : ℝ)
    (171126409 / 100000000 : ℝ) (171 / 5000000000 : ℝ) (7893 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (69 / 80 : ℝ)) (5612519 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (691 / 800 : ℝ) (59301 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (691 / 800 : ℝ))) h 2
    have he :
        (Real.exp (691 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (691 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (5612519 / 1000000 : ℝ) - (691 / 800 : ℝ) / 2) / 32)
      (171126409 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_691 :
    ∀ u : ℝ, (691 / 800 : ℝ) ≤ u → u ≤ (173 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (7609 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (691 / 800 : ℝ) (173 / 200 : ℝ) (703321 / 125000 : ℝ) (5640658250049 / 1000000000000 : ℝ)
    (42839783 / 25000000 : ℝ) (41 / 1250000000 : ℝ) (7609 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (691 / 800 : ℝ)) (703321 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (173 / 200 : ℝ) (2375007 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (173 / 200 : ℝ))) h 2
    have he :
        (Real.exp (173 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (173 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (703321 / 125000 : ℝ) - (173 / 200 : ℝ) / 2) / 32)
      (42839783 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_692 :
    ∀ u : ℝ, (173 / 200 : ℝ) ≤ u → u ≤ (693 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (7323 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (173 / 200 : ℝ) (693 / 800 : ℝ) (1410163 / 250000 : ℝ) (5654774612529 / 1000000000000 : ℝ)
    (85796381 / 50000000 : ℝ) (157 / 5000000000 : ℝ) (7323 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (173 / 200 : ℝ)) (1410163 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (693 / 800 : ℝ) (2377977 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (693 / 800 : ℝ))) h 2
    have he :
        (Real.exp (693 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (693 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1410163 / 250000 : ℝ) - (693 / 800 : ℝ) / 2) / 32)
      (85796381 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_693 :
    ∀ u : ℝ, (693 / 800 : ℝ) ≤ u → u ≤ (347 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (7033 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (693 / 800 : ℝ) (347 / 400 : ℝ) (5654771 / 1000000 : ℝ) (88577069161 / 15625000000 : ℝ)
    (1718273 / 1000000 : ℝ) (3 / 100000000 : ℝ) (7033 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (693 / 800 : ℝ)) (5654771 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (347 / 400 : ℝ) (297619 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (347 / 400 : ℝ))) h 2
    have he :
        (Real.exp (347 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (347 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (5654771 / 1000000 : ℝ) - (347 / 400 : ℝ) / 2) / 32)
      (1718273 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_694 :
    ∀ u : ℝ, (347 / 400 : ℝ) ≤ u → u ≤ (139 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (6787 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (347 / 400 : ℝ) (139 / 160 : ℝ) (2834463 / 500000 : ℝ) (56831222449 / 10000000000 : ℝ)
    (86031383 / 50000000 : ℝ) (9 / 312500000 : ℝ) (6787 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (347 / 400 : ℝ)) (2834463 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (139 / 160 : ℝ) (238393 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (139 / 160 : ℝ))) h 2
    have he :
        (Real.exp (139 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (139 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2834463 / 500000 : ℝ) - (139 / 160 : ℝ) / 2) / 32)
      (86031383 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_695 :
    ∀ u : ℝ, (139 / 160 : ℝ) ≤ u → u ≤ (87 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1303 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (139 / 160 : ℝ) (87 / 100 : ℝ) (1420779 / 250000 : ℝ) (5697344121921 / 1000000000000 : ℝ)
    (172299147 / 100000000 : ℝ) (11 / 400000000 : ℝ) (1303 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (139 / 160 : ℝ)) (1420779 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (87 / 100 : ℝ) (2386911 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (87 / 100 : ℝ))) h 2
    have he :
        (Real.exp (87 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (87 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1420779 / 250000 : ℝ) - (87 / 100 : ℝ) / 2) / 32)
      (172299147 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_696 :
    ∀ u : ℝ, (87 / 100 : ℝ) ≤ u → u ≤ (697 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (6263 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (87 / 100 : ℝ) (697 / 800 : ℝ) (5697341 / 1000000 : ℝ) (5711607670609 / 1000000000000 : ℝ)
    (34507289 / 20000000 : ℝ) (263 / 10000000000 : ℝ) (6263 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (87 / 100 : ℝ)) (5697341 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (697 / 800 : ℝ) (2389897 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (697 / 800 : ℝ))) h 2
    have he :
        (Real.exp (697 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (697 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (5697341 / 1000000 : ℝ) - (697 / 800 : ℝ) / 2) / 32)
      (34507289 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_697 :
    ∀ u : ℝ, (697 / 800 : ℝ) ≤ u → u ≤ (349 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (377 / 6250000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (697 / 800 : ℝ) (349 / 400 : ℝ) (2855801 / 500000 : ℝ) (1431475852249 / 250000000000 : ℝ)
    (4319367 / 2500000 : ℝ) (63 / 2500000000 : ℝ) (377 / 6250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (697 / 800 : ℝ)) (2855801 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (349 / 400 : ℝ) (1196443 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (349 / 400 : ℝ))) h 2
    have he :
        (Real.exp (349 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (349 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2855801 / 500000 : ℝ) - (349 / 400 : ℝ) / 2) / 32)
      (4319367 / 2500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_698 :
    ∀ u : ℝ, (349 / 400 : ℝ) ≤ u → u ≤ (699 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (5799 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (349 / 400 : ℝ) (699 / 800 : ℝ) (5725899 / 1000000 : ℝ) (5740236182641 / 1000000000000 : ℝ)
    (34602771 / 20000000 : ℝ) (241 / 10000000000 : ℝ) (5799 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (349 / 400 : ℝ)) (5725899 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (699 / 800 : ℝ) (2395879 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (699 / 800 : ℝ))) h 2
    have he :
        (Real.exp (699 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (699 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (5725899 / 1000000 : ℝ) - (699 / 800 : ℝ) / 2) / 32)
      (34602771 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_699 :
    ∀ u : ℝ, (699 / 800 : ℝ) ≤ u → u ≤ (7 / 8 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1397 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (699 / 800 : ℝ) (7 / 8 : ℝ) (717529 / 125000 : ℝ) (359662878961 / 62500000000 : ℝ)
    (86626987 / 50000000 : ℝ) (231 / 10000000000 : ℝ) (1397 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (699 / 800 : ℝ)) (717529 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (7 / 8 : ℝ) (599719 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (7 / 8 : ℝ))) h 2
    have he :
        (Real.exp (7 / 8 : ℝ)) ^ 2 =
          Real.exp (2 * (7 / 8 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (717529 / 125000 : ℝ) - (7 / 8 : ℝ) / 2) / 32)
      (86626987 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_680
#print axioms hpThetaEnergyUpper_interval_699

end HodgeProofHP
