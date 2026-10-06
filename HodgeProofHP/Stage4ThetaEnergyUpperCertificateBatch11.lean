import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_220 :
    ∀ u : ℝ, (11 / 40 : ℝ) ≤ u → u ≤ (221 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (86887901 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (11 / 40 : ℝ) (221 / 800 : ℝ) (1733253 / 1000000 : ℝ) (434398309921 / 250000000000 : ℝ)
    (118028867 / 100000000 : ℝ) (3106393 / 625000000 : ℝ) (86887901 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (11 / 40 : ℝ)) (1733253 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (221 / 800 : ℝ) (659089 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (221 / 800 : ℝ))) h 2
    have he :
        (Real.exp (221 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (221 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1733253 / 1000000 : ℝ) - (221 / 800 : ℝ) / 2) / 32)
      (118028867 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_221 :
    ∀ u : ℝ, (221 / 800 : ℝ) ≤ u → u ≤ (111 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (86276611 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (221 / 800 : ℝ) (111 / 400 : ℝ) (1737591 / 1000000 : ℝ) (1741943309929 / 1000000000000 : ℝ)
    (29519203 / 25000000 : ℝ) (24530263 / 5000000000 : ℝ) (86276611 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (221 / 800 : ℝ)) (1737591 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (111 / 400 : ℝ) (1319827 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (111 / 400 : ℝ))) h 2
    have he :
        (Real.exp (111 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (111 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1737591 / 1000000 : ℝ) - (111 / 400 : ℝ) / 2) / 32)
      (29519203 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_222 :
    ∀ u : ℝ, (111 / 400 : ℝ) ≤ u → u ≤ (223 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (85666007 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (111 / 400 : ℝ) (223 / 800 : ℝ) (87097 / 50000 : ℝ) (1746301461529 / 1000000000000 : ℝ)
    (14765613 / 12500000 : ℝ) (48425377 / 10000000000 : ℝ) (85666007 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (111 / 400 : ℝ)) (87097 / 50000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (223 / 800 : ℝ) (1321477 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (223 / 800 : ℝ))) h 2
    have he :
        (Real.exp (223 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (223 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (87097 / 50000 : ℝ) - (223 / 800 : ℝ) / 2) / 32)
      (14765613 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_223 :
    ∀ u : ℝ, (223 / 800 : ℝ) ≤ u → u ≤ (7 / 25 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (85056553 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (223 / 800 : ℝ) (7 / 25 : ℝ) (1746301 / 1000000 : ℝ) (17506729969 / 10000000000 : ℝ)
    (23634631 / 20000000 : ℝ) (47796647 / 10000000000 : ℝ) (85056553 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (223 / 800 : ℝ)) (1746301 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (7 / 25 : ℝ) (132313 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (7 / 25 : ℝ))) h 2
    have he :
        (Real.exp (7 / 25 : ℝ)) ^ 2 =
          Real.exp (2 * (7 / 25 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1746301 / 1000000 : ℝ) - (7 / 25 : ℝ) / 2) / 32)
      (23634631 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_224 :
    ∀ u : ℝ, (7 / 25 : ℝ) ≤ u → u ≤ (9 / 32 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (84448499 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (7 / 25 : ℝ) (9 / 32 : ℝ) (109417 / 62500 : ℝ) (70202211849 / 40000000000 : ℝ)
    (59110771 / 50000000 : ℝ) (23587297 / 5000000000 : ℝ) (84448499 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (7 / 25 : ℝ)) (109417 / 62500 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (9 / 32 : ℝ) (264957 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (9 / 32 : ℝ))) h 2
    have he :
        (Real.exp (9 / 32 : ℝ)) ^ 2 =
          Real.exp (2 * (9 / 32 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (109417 / 62500 : ℝ) - (9 / 32 : ℝ) / 2) / 32)
      (59110771 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_225 :
    ∀ u : ℝ, (9 / 32 : ℝ) ≤ u → u ≤ (113 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (4192081 / 5000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (9 / 32 : ℝ) (113 / 400 : ℝ) (877527 / 500000 : ℝ) (439862094841 / 250000000000 : ℝ)
    (29567519 / 25000000 : ℝ) (11639759 / 2500000000 : ℝ) (4192081 / 5000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (9 / 32 : ℝ)) (877527 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (113 / 400 : ℝ) (663221 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (113 / 400 : ℝ))) h 2
    have he :
        (Real.exp (113 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (113 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (877527 / 500000 : ℝ) - (113 / 400 : ℝ) / 2) / 32)
      (29567519 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_226 :
    ∀ u : ℝ, (113 / 400 : ℝ) ≤ u → u ≤ (227 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (10404491 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (113 / 400 : ℝ) (227 / 800 : ℝ) (1759447 / 1000000 : ℝ) (1763852266201 / 1000000000000 : ℝ)
    (59159379 / 50000000 : ℝ) (45949917 / 10000000000 : ℝ) (10404491 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (113 / 400 : ℝ)) (1759447 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (227 / 800 : ℝ) (1328101 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (227 / 800 : ℝ))) h 2
    have he :
        (Real.exp (227 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (227 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1759447 / 1000000 : ℝ) - (227 / 800 : ℝ) / 2) / 32)
      (59159379 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_227 :
    ∀ u : ℝ, (227 / 800 : ℝ) ≤ u → u ≤ (57 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (82631809 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (227 / 800 : ℝ) (57 / 200 : ℝ) (1763851 / 1000000 : ℝ) (1768269636169 / 1000000000000 : ℝ)
    (29591897 / 25000000 : ℝ) (45347199 / 10000000000 : ℝ) (82631809 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (227 / 800 : ℝ)) (1763851 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (57 / 200 : ℝ) (1329763 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (57 / 200 : ℝ))) h 2
    have he :
        (Real.exp (57 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (57 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1763851 / 1000000 : ℝ) - (57 / 200 : ℝ) / 2) / 32)
      (29591897 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_228 :
    ∀ u : ℝ, (57 / 200 : ℝ) ≤ u → u ≤ (229 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (41014181 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (57 / 200 : ℝ) (229 / 800 : ℝ) (1768267 / 1000000 : ℝ) (443173798369 / 250000000000 : ℝ)
    (118416577 / 100000000 : ℝ) (11187677 / 2500000000 : ℝ) (41014181 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (57 / 200 : ℝ)) (1768267 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (229 / 800 : ℝ) (665713 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (229 / 800 : ℝ))) h 2
    have he :
        (Real.exp (229 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (229 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1768267 / 1000000 : ℝ) - (229 / 800 : ℝ) / 2) / 32)
      (118416577 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_229 :
    ∀ u : ℝ, (229 / 800 : ℝ) ≤ u → u ≤ (23 / 80 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (81426491 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (229 / 800 : ℝ) (23 / 80 : ℝ) (1772693 / 1000000 : ℝ) (1777131614281 / 1000000000000 : ℝ)
    (118465703 / 100000000 : ℝ) (4416067 / 1000000000 : ℝ) (81426491 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (229 / 800 : ℝ)) (1772693 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (23 / 80 : ℝ) (1333091 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (23 / 80 : ℝ))) h 2
    have he :
        (Real.exp (23 / 80 : ℝ)) ^ 2 =
          Real.exp (2 * (23 / 80 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1772693 / 1000000 : ℝ) - (23 / 80 : ℝ) / 2) / 32)
      (118465703 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_230 :
    ∀ u : ℝ, (23 / 80 : ℝ) ≤ u → u ≤ (231 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (3233039 / 4000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (23 / 80 : ℝ) (231 / 800 : ℝ) (177713 / 100000 : ℝ) (445394729641 / 250000000000 : ℝ)
    (118514977 / 100000000 : ℝ) (4357691 / 1000000000 : ℝ) (3233039 / 4000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (23 / 80 : ℝ)) (177713 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (231 / 800 : ℝ) (667379 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (231 / 800 : ℝ))) h 2
    have he :
        (Real.exp (231 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (231 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (177713 / 100000 : ℝ) - (231 / 800 : ℝ) / 2) / 32)
      (118514977 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_231 :
    ∀ u : ℝ, (231 / 800 : ℝ) ≤ u → u ≤ (29 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (80227161 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (231 / 800 : ℝ) (29 / 100 : ℝ) (890789 / 500000 : ℝ) (111627487449 / 62500000000 : ℝ)
    (296411 / 250000 : ℝ) (2687461 / 625000000 : ℝ) (80227161 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (231 / 800 : ℝ)) (890789 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (29 / 100 : ℝ) (334107 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (29 / 100 : ℝ))) h 2
    have he :
        (Real.exp (29 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (29 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (890789 / 500000 : ℝ) - (29 / 100 : ℝ) / 2) / 32)
      (296411 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_232 :
    ∀ u : ℝ, (29 / 100 : ℝ) ≤ u → u ≤ (233 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (79629499 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (29 / 100 : ℝ) (233 / 800 : ℝ) (893019 / 500000 : ℝ) (179051161 / 100000000 : ℝ)
    (118613983 / 100000000 : ℝ) (424279 / 100000000 : ℝ) (79629499 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (29 / 100 : ℝ)) (893019 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (233 / 800 : ℝ) (13381 / 10000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (233 / 800 : ℝ))) h 2
    have he :
        (Real.exp (233 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (233 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (893019 / 500000 : ℝ) - (233 / 800 : ℝ) / 2) / 32)
      (118613983 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_233 :
    ∀ u : ℝ, (233 / 800 : ℝ) ≤ u → u ≤ (117 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (7903297 / 10000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (233 / 800 : ℝ) (117 / 400 : ℝ) (1790509 / 1000000 : ℝ) (1794991691529 / 1000000000000 : ℝ)
    (23732743 / 20000000 : ℝ) (10465643 / 2500000000 : ℝ) (7903297 / 10000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (233 / 800 : ℝ)) (1790509 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (117 / 400 : ℝ) (1339773 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (117 / 400 : ℝ))) h 2
    have he :
        (Real.exp (117 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (117 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1790509 / 1000000 : ℝ) - (117 / 400 : ℝ) / 2) / 32)
      (23732743 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_234 :
    ∀ u : ℝ, (117 / 400 : ℝ) ≤ u → u ≤ (47 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1960963 / 2500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (117 / 400 : ℝ) (47 / 160 : ℝ) (179499 / 100000 : ℝ) (1799485419601 / 1000000000000 : ℝ)
    (7419599 / 6250000 : ℝ) (41303483 / 10000000000 : ℝ) (1960963 / 2500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (117 / 400 : ℝ)) (179499 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (47 / 160 : ℝ) (1341449 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (47 / 160 : ℝ))) h 2
    have he :
        (Real.exp (47 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (47 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (179499 / 100000 : ℝ) - (47 / 160 : ℝ) / 2) / 32)
      (7419599 / 6250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_235 :
    ∀ u : ℝ, (47 / 160 : ℝ) ≤ u → u ≤ (59 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (77845079 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (47 / 160 : ℝ) (59 / 200 : ℝ) (449871 / 250000 : ℝ) (1803990138129 / 1000000000000 : ℝ)
    (950109 / 800000 : ℝ) (20375101 / 5000000000 : ℝ) (77845079 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (47 / 160 : ℝ)) (449871 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (59 / 200 : ℝ) (1343127 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (59 / 200 : ℝ))) h 2
    have he :
        (Real.exp (59 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (59 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (449871 / 250000 : ℝ) - (59 / 200 : ℝ) / 2) / 32)
      (950109 / 800000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_236 :
    ∀ u : ℝ, (59 / 200 : ℝ) ≤ u → u ≤ (237 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (19313363 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (59 / 200 : ℝ) (237 / 800 : ℝ) (450997 / 250000 : ℝ) (1808505867249 / 1000000000000 : ℝ)
    (29703451 / 25000000 : ℝ) (40203067 / 10000000000 : ℝ) (19313363 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (59 / 200 : ℝ)) (450997 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (237 / 800 : ℝ) (1344807 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (237 / 800 : ℝ))) h 2
    have he :
        (Real.exp (237 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (237 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (450997 / 250000 : ℝ) - (237 / 800 : ℝ) / 2) / 32)
      (29703451 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_237 :
    ∀ u : ℝ, (237 / 800 : ℝ) ≤ u → u ≤ (119 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (76663141 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (237 / 800 : ℝ) (119 / 400 : ℝ) (226063 / 125000 : ℝ) (1813032627121 / 1000000000000 : ℝ)
    (23772829 / 20000000 : ℝ) (19830887 / 5000000000 : ℝ) (76663141 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (237 / 800 : ℝ)) (226063 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (119 / 400 : ℝ) (1346489 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (119 / 400 : ℝ))) h 2
    have he :
        (Real.exp (119 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (119 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (226063 / 125000 : ℝ) - (119 / 400 : ℝ) / 2) / 32)
      (23772829 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_238 :
    ∀ u : ℝ, (119 / 400 : ℝ) ≤ u → u ≤ (239 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (15214947 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (119 / 400 : ℝ) (239 / 800 : ℝ) (181303 / 100000 : ℝ) (1817570437929 / 1000000000000 : ℝ)
    (118914623 / 100000000 : ℝ) (4890819 / 1250000000 : ℝ) (15214947 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (119 / 400 : ℝ)) (181303 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (239 / 800 : ℝ) (1348173 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (239 / 800 : ℝ))) h 2
    have he :
        (Real.exp (239 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (239 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (181303 / 100000 : ℝ) - (239 / 800 : ℝ) / 2) / 32)
      (118914623 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_239 :
    ∀ u : ℝ, (239 / 800 : ℝ) ≤ u → u ≤ (3 / 10 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (15097493 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (239 / 800 : ℝ) (3 / 10 : ℝ) (1817569 / 1000000 : ℝ) (1822119319881 / 1000000000000 : ℝ)
    (4758611 / 4000000 : ℝ) (4824621 / 1250000000 : ℝ) (15097493 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (239 / 800 : ℝ)) (1817569 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (3 / 10 : ℝ) (1349859 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (3 / 10 : ℝ))) h 2
    have he :
        (Real.exp (3 / 10 : ℝ)) ^ 2 =
          Real.exp (2 * (3 / 10 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1817569 / 1000000 : ℝ) - (3 / 10 : ℝ) / 2) / 32)
      (4758611 / 4000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_220
#print axioms hpThetaEnergyUpper_interval_239

end HodgeProofHP
