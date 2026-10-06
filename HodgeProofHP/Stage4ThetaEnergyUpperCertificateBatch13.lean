import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_260 :
    ∀ u : ℝ, (13 / 40 : ℝ) ≤ u → u ≤ (261 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (63577567 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (13 / 40 : ℝ) (261 / 800 : ℝ) (95777 / 50000 : ℝ) (480084080161 / 250000000000 : ℝ)
    (24013039 / 20000000 : ℝ) (14375463 / 5000000000 : ℝ) (63577567 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (13 / 40 : ℝ)) (95777 / 50000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (261 / 800 : ℝ) (692881 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (261 / 800 : ℝ))) h 2
    have he :
        (Real.exp (261 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (261 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (95777 / 50000 : ℝ) - (261 / 800 : ℝ) / 2) / 32)
      (24013039 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_261 :
    ∀ u : ℝ, (261 / 800 : ℝ) ≤ u → u ≤ (131 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (157581 / 250000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (261 / 800 : ℝ) (131 / 400 : ℝ) (384067 / 200000 : ℝ) (30080392969 / 15625000000 : ℝ)
    (60059677 / 50000000 : ℝ) (1771187 / 625000000 : ℝ) (157581 / 250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (261 / 800 : ℝ)) (384067 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (131 / 400 : ℝ) (173437 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (131 / 400 : ℝ))) h 2
    have he :
        (Real.exp (131 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (131 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (384067 / 200000 : ℝ) - (131 / 400 : ℝ) / 2) / 32)
      (60059677 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_262 :
    ∀ u : ℝ, (131 / 400 : ℝ) ≤ u → u ≤ (263 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (62489103 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (131 / 400 : ℝ) (263 / 800 : ℝ) (962571 / 500000 : ℝ) (1929962771361 / 1000000000000 : ℝ)
    (120173679 / 100000000 : ℝ) (27931907 / 10000000000 : ℝ) (62489103 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (131 / 400 : ℝ)) (962571 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (263 / 800 : ℝ) (1389231 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (263 / 800 : ℝ))) h 2
    have he :
        (Real.exp (263 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (263 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (962571 / 500000 : ℝ) - (263 / 800 : ℝ) / 2) / 32)
      (120173679 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_263 :
    ∀ u : ℝ, (263 / 800 : ℝ) ≤ u → u ≤ (33 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (61948189 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (263 / 800 : ℝ) (33 / 100 : ℝ) (1929961 / 1000000 : ℝ) (1934794758961 / 1000000000000 : ℝ)
    (12022817 / 10000000 : ℝ) (13764817 / 5000000000 : ℝ) (61948189 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (263 / 800 : ℝ)) (1929961 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (33 / 100 : ℝ) (1390969 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (33 / 100 : ℝ))) h 2
    have he :
        (Real.exp (33 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (33 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1929961 / 1000000 : ℝ) - (33 / 100 : ℝ) / 2) / 32)
      (12022817 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_264 :
    ∀ u : ℝ, (33 / 100 : ℝ) ≤ u → u ≤ (53 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (7676149 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (33 / 100 : ℝ) (53 / 160 : ℝ) (241849 / 125000 : ℝ) (121227223329 / 62500000000 : ℝ)
    (30070707 / 25000000 : ℝ) (27132127 / 10000000000 : ℝ) (7676149 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (33 / 100 : ℝ)) (241849 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (53 / 160 : ℝ) (348177 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (53 / 160 : ℝ))) h 2
    have he :
        (Real.exp (53 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (53 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (241849 / 125000 : ℝ) - (53 / 160 : ℝ) / 2) / 32)
      (30070707 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_265 :
    ∀ u : ℝ, (53 / 160 : ℝ) ≤ u → u ≤ (133 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (30436323 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (53 / 160 : ℝ) (133 / 400 : ℝ) (387927 / 200000 : ℝ) (777796321 / 400000000 : ℝ)
    (120337651 / 100000000 : ℝ) (26739363 / 10000000000 : ℝ) (30436323 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (53 / 160 : ℝ)) (387927 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (133 / 400 : ℝ) (27889 / 20000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (133 / 400 : ℝ))) h 2
    have he :
        (Real.exp (133 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (133 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (387927 / 200000 : ℝ) - (133 / 400 : ℝ) / 2) / 32)
      (120337651 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_266 :
    ∀ u : ℝ, (133 / 400 : ℝ) ≤ u → u ≤ (267 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (60338523 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (133 / 400 : ℝ) (267 / 800 : ℝ) (194449 / 100000 : ℝ) (77974419121 / 40000000000 : ℝ)
    (60196321 / 50000000 : ℝ) (26351283 / 10000000000 : ℝ) (60338523 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (133 / 400 : ℝ)) (194449 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (267 / 800 : ℝ) (279239 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (267 / 800 : ℝ))) h 2
    have he :
        (Real.exp (267 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (267 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (194449 / 100000 : ℝ) - (267 / 800 : ℝ) / 2) / 32)
      (60196321 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_267 :
    ∀ u : ℝ, (267 / 800 : ℝ) ≤ u → u ≤ (67 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (7475801 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (267 / 800 : ℝ) (67 / 200 : ℝ) (1949357 / 1000000 : ℝ) (1954239039481 / 1000000000000 : ℝ)
    (602239 / 500000 : ℝ) (25967857 / 10000000000 : ℝ) (7475801 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (267 / 800 : ℝ)) (1949357 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (67 / 200 : ℝ) (1397941 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (67 / 200 : ℝ))) h 2
    have he :
        (Real.exp (67 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (67 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1949357 / 1000000 : ℝ) - (67 / 200 : ℝ) / 2) / 32)
      (602239 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_268 :
    ∀ u : ℝ, (67 / 200 : ℝ) ≤ u → u ≤ (269 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (7409547 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (67 / 200 : ℝ) (269 / 800 : ℝ) (1954237 / 1000000 : ℝ) (1959129296721 / 1000000000000 : ℝ)
    (3765723 / 3125000 : ℝ) (6397243 / 2500000000 : ℝ) (7409547 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (67 / 200 : ℝ)) (1954237 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (269 / 800 : ℝ) (1399689 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (269 / 800 : ℝ))) h 2
    have he :
        (Real.exp (269 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (269 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1954237 / 1000000 : ℝ) - (269 / 800 : ℝ) / 2) / 32)
      (3765723 / 3125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_269 :
    ∀ u : ℝ, (269 / 800 : ℝ) ≤ u → u ≤ (27 / 80 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (14687211 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (269 / 800 : ℝ) (27 / 80 : ℝ) (1959129 / 1000000 : ℝ) (76720081 / 39062500 : ℝ)
    (1506983 / 1250000 : ℝ) (1260733 / 500000000 : ℝ) (14687211 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (269 / 800 : ℝ)) (1959129 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (27 / 80 : ℝ) (8759 / 6250 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (27 / 80 : ℝ))) h 2
    have he :
        (Real.exp (27 / 80 : ℝ)) ^ 2 =
          Real.exp (2 * (27 / 80 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1959129 / 1000000 : ℝ) - (27 / 80 : ℝ) / 2) / 32)
      (1506983 / 1250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_270 :
    ∀ u : ℝ, (27 / 80 : ℝ) ≤ u → u ≤ (271 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (58223813 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (27 / 80 : ℝ) (271 / 800 : ℝ) (30688 / 15625 : ℝ) (1968950595249 / 1000000000000 : ℝ)
    (1206143 / 1000000 : ℝ) (4968993 / 2000000000 : ℝ) (58223813 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (27 / 80 : ℝ)) (30688 / 15625 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (271 / 800 : ℝ) (1403193 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (271 / 800 : ℝ))) h 2
    have he :
        (Real.exp (271 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (271 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (30688 / 15625 : ℝ) - (271 / 800 : ℝ) / 2) / 32)
      (1206143 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_271 :
    ∀ u : ℝ, (271 / 800 : ℝ) ≤ u → u ≤ (17 / 50 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (11540147 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (271 / 800 : ℝ) (17 / 50 : ℝ) (1968949 / 1000000 : ℝ) (123367430169 / 62500000000 : ℝ)
    (120670151 / 100000000 : ℝ) (24479617 / 10000000000 : ℝ) (11540147 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (271 / 800 : ℝ)) (1968949 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (17 / 50 : ℝ) (351237 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (17 / 50 : ℝ))) h 2
    have he :
        (Real.exp (17 / 50 : ℝ)) ^ 2 =
          Real.exp (2 * (17 / 50 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1968949 / 1000000 : ℝ) - (17 / 50 : ℝ) / 2) / 32)
      (120670151 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_272 :
    ∀ u : ℝ, (17 / 50 : ℝ) ≤ u → u ≤ (273 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (57180189 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (17 / 50 : ℝ) (273 / 800 : ℝ) (1973877 / 1000000 : ℝ) (79152758281 / 40000000000 : ℝ)
    (120726159 / 100000000 : ℝ) (12059401 / 5000000000 : ℝ) (57180189 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (17 / 50 : ℝ)) (1973877 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (273 / 800 : ℝ) (281341 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (273 / 800 : ℝ))) h 2
    have he :
        (Real.exp (273 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (273 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1973877 / 1000000 : ℝ) - (273 / 800 : ℝ) / 2) / 32)
      (120726159 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_273 :
    ∀ u : ℝ, (273 / 800 : ℝ) ≤ u → u ≤ (137 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (56662061 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (273 / 800 : ℝ) (137 / 400 : ℝ) (989409 / 500000 : ℝ) (79350946249 / 40000000000 : ℝ)
    (60391173 / 50000000 : ℝ) (23762343 / 10000000000 : ℝ) (56662061 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (273 / 800 : ℝ)) (989409 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (137 / 400 : ℝ) (281693 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (137 / 400 : ℝ))) h 2
    have he :
        (Real.exp (137 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (137 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (989409 / 500000 : ℝ) - (137 / 400 : ℝ) / 2) / 32)
      (60391173 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_274 :
    ∀ u : ℝ, (137 / 400 : ℝ) ≤ u → u ≤ (11 / 32 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (701829 / 1250000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (137 / 400 : ℝ) (11 / 32 : ℝ) (1983771 / 1000000 : ℝ) (1988740191529 / 1000000000000 : ℝ)
    (60419351 / 50000000 : ℝ) (11705133 / 5000000000 : ℝ) (701829 / 1250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (137 / 400 : ℝ)) (1983771 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (11 / 32 : ℝ) (1410227 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (11 / 32 : ℝ))) h 2
    have he :
        (Real.exp (11 / 32 : ℝ)) ^ 2 =
          Real.exp (2 * (11 / 32 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1983771 / 1000000 : ℝ) - (11 / 32 : ℝ) / 2) / 32)
      (60419351 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_275 :
    ∀ u : ℝ, (11 / 32 : ℝ) ≤ u → u ≤ (69 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (278163 / 500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (11 / 32 : ℝ) (69 / 200 : ℝ) (1988737 / 1000000 : ℝ) (19937157601 / 10000000000 : ℝ)
    (120895239 / 100000000 : ℝ) (11531231 / 5000000000 : ℝ) (278163 / 500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (11 / 32 : ℝ)) (1988737 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (69 / 200 : ℝ) (141199 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (69 / 200 : ℝ))) h 2
    have he :
        (Real.exp (69 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (69 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1988737 / 1000000 : ℝ) - (69 / 200 : ℝ) / 2) / 32)
      (120895239 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_276 :
    ∀ u : ℝ, (69 / 200 : ℝ) ≤ u → u ≤ (277 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (3445109 / 6250000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (69 / 200 : ℝ) (277 / 800 : ℝ) (398743 / 200000 : ℝ) (1998708855049 / 1000000000000 : ℝ)
    (15118993 / 12500000 : ℝ) (11359487 / 5000000000 : ℝ) (3445109 / 6250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (69 / 200 : ℝ)) (398743 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (277 / 800 : ℝ) (1413757 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (277 / 800 : ℝ))) h 2
    have he :
        (Real.exp (277 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (277 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (398743 / 200000 : ℝ) - (277 / 800 : ℝ) / 2) / 32)
      (15118993 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_277 :
    ∀ u : ℝ, (277 / 800 : ℝ) ≤ u → u ≤ (139 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (27306481 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (277 / 800 : ℝ) (139 / 400 : ℝ) (999353 / 500000 : ℝ) (3205937641 / 1600000000 : ℝ)
    (12100883 / 10000000 : ℝ) (2797461 / 1250000000 : ℝ) (27306481 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (277 / 800 : ℝ)) (999353 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (139 / 400 : ℝ) (56621 / 40000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (139 / 400 : ℝ))) h 2
    have he :
        (Real.exp (139 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (139 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (999353 / 500000 : ℝ) - (139 / 400 : ℝ) / 2) / 32)
      (12100883 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_278 :
    ∀ u : ℝ, (139 / 400 : ℝ) ≤ u → u ≤ (279 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (54106651 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (139 / 400 : ℝ) (279 / 800 : ℝ) (2003709 / 1000000 : ℝ) (80349004681 / 40000000000 : ℝ)
    (60532943 / 50000000 : ℝ) (11022317 / 5000000000 : ℝ) (54106651 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (139 / 400 : ℝ)) (2003709 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (279 / 800 : ℝ) (283459 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (279 / 800 : ℝ))) h 2
    have he :
        (Real.exp (279 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (279 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2003709 / 1000000 : ℝ) - (279 / 800 : ℝ) / 2) / 32)
      (60532943 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_279 :
    ∀ u : ℝ, (279 / 800 : ℝ) ≤ u → u ≤ (7 / 20 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (53603049 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (279 / 800 : ℝ) (7 / 20 : ℝ) (502181 / 250000 : ℝ) (125859624289 / 62500000000 : ℝ)
    (121123111 / 100000000 : ℝ) (10856891 / 5000000000 : ℝ) (53603049 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (279 / 800 : ℝ)) (502181 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (7 / 20 : ℝ) (354767 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (7 / 20 : ℝ))) h 2
    have he :
        (Real.exp (7 / 20 : ℝ)) ^ 2 =
          Real.exp (2 * (7 / 20 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (502181 / 250000 : ℝ) - (7 / 20 : ℝ) / 2) / 32)
      (121123111 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_260
#print axioms hpThetaEnergyUpper_interval_279

end HodgeProofHP
