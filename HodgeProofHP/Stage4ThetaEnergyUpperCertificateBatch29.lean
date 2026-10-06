import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_580 :
    ∀ u : ℝ, (29 / 40 : ℝ) ≤ u → u ≤ (581 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (8923 / 3125000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (29 / 40 : ℝ) (581 / 800 : ℝ) (2131557 / 500000 : ℝ) (1068446793649 / 250000000000 : ℝ)
    (37556491 / 25000000 : ℝ) (22089 / 10000000000 : ℝ) (8923 / 3125000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (29 / 40 : ℝ)) (2131557 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (581 / 800 : ℝ) (1033657 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (581 / 800 : ℝ))) h 2
    have he :
        (Real.exp (581 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (581 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2131557 / 500000 : ℝ) - (581 / 800 : ℝ) / 2) / 32)
      (37556491 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_581 :
    ∀ u : ℝ, (581 / 800 : ℝ) ≤ u → u ≤ (291 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (55553 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (581 / 800 : ℝ) (291 / 400 : ℝ) (854757 / 200000 : ℝ) (428448601 / 100000000 : ℝ)
    (15038041 / 10000000 : ℝ) (10687 / 5000000000 : ℝ) (55553 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (581 / 800 : ℝ)) (854757 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (291 / 400 : ℝ) (20699 / 10000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (291 / 400 : ℝ))) h 2
    have he :
        (Real.exp (291 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (291 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (854757 / 200000 : ℝ) - (291 / 400 : ℝ) / 2) / 32)
      (15038041 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_582 :
    ∀ u : ℝ, (291 / 400 : ℝ) ≤ u → u ≤ (583 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (27019 / 10000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (291 / 400 : ℝ) (583 / 800 : ℝ) (4284483 / 1000000 : ℝ) (4295210655121 / 1000000000000 : ℝ)
    (150535413 / 100000000 : ℝ) (20681 / 10000000000 : ℝ) (27019 / 10000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (291 / 400 : ℝ)) (4284483 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (583 / 800 : ℝ) (2072489 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (583 / 800 : ℝ))) h 2
    have he :
        (Real.exp (583 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (583 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4284483 / 1000000 : ℝ) - (583 / 800 : ℝ) / 2) / 32)
      (150535413 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_583 :
    ∀ u : ℝ, (583 / 800 : ℝ) ≤ u → u ≤ (73 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (131401 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (583 / 800 : ℝ) (73 / 100 : ℝ) (4295207 / 1000000 : ℝ) (4305961156561 / 1000000000000 : ℝ)
    (1883637 / 1250000 : ℝ) (20009 / 10000000000 : ℝ) (131401 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (583 / 800 : ℝ)) (4295207 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (73 / 100 : ℝ) (2075081 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (73 / 100 : ℝ))) h 2
    have he :
        (Real.exp (73 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (73 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4295207 / 1000000 : ℝ) - (73 / 100 : ℝ) / 2) / 32)
      (1883637 / 1250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_584 :
    ∀ u : ℝ, (73 / 100 : ℝ) ≤ u → u ≤ (117 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (31949 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (73 / 100 : ℝ) (117 / 160 : ℝ) (4305959 / 1000000 : ℝ) (4316741716329 / 1000000000000 : ℝ)
    (150847083 / 100000000 : ℝ) (19357 / 10000000000 : ℝ) (31949 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (73 / 100 : ℝ)) (4305959 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (117 / 160 : ℝ) (2077677 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (117 / 160 : ℝ))) h 2
    have he :
        (Real.exp (117 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (117 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4305959 / 1000000 : ℝ) - (117 / 160 : ℝ) / 2) / 32)
      (150847083 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_585 :
    ∀ u : ℝ, (117 / 160 : ℝ) ≤ u → u ≤ (293 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (248549 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (117 / 160 : ℝ) (293 / 400 : ℝ) (4316737 / 1000000 : ℝ) (6924070521 / 1600000000 : ℝ)
    (151003753 / 100000000 : ℝ) (4681 / 2500000000 : ℝ) (248549 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (117 / 160 : ℝ)) (4316737 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (293 / 400 : ℝ) (83211 / 40000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (293 / 400 : ℝ))) h 2
    have he :
        (Real.exp (293 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (293 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4316737 / 1000000 : ℝ) - (293 / 400 : ℝ) / 2) / 32)
      (151003753 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_586 :
    ∀ u : ℝ, (293 / 400 : ℝ) ≤ u → u ≤ (587 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (241691 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (293 / 400 : ℝ) (587 / 800 : ℝ) (4327543 / 1000000 : ℝ) (4338376597129 / 1000000000000 : ℝ)
    (151161 / 100000 : ℝ) (18111 / 10000000000 : ℝ) (241691 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (293 / 400 : ℝ)) (4327543 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (587 / 800 : ℝ) (2082877 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (587 / 800 : ℝ))) h 2
    have he :
        (Real.exp (587 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (587 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4327543 / 1000000 : ℝ) - (587 / 800 : ℝ) / 2) / 32)
      (151161 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_587 :
    ∀ u : ℝ, (587 / 800 : ℝ) ≤ u → u ≤ (147 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (117497 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (587 / 800 : ℝ) (147 / 200 : ℝ) (34707 / 8000 : ℝ) (1087308793081 / 250000000000 : ℝ)
    (75659399 / 50000000 : ℝ) (4379 / 2500000000 : ℝ) (117497 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (587 / 800 : ℝ)) (34707 / 8000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (147 / 200 : ℝ) (1042741 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (147 / 200 : ℝ))) h 2
    have he :
        (Real.exp (147 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (147 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (34707 / 8000 : ℝ) - (147 / 200 : ℝ) / 2) / 32)
      (75659399 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_588 :
    ∀ u : ℝ, (147 / 200 : ℝ) ≤ u → u ≤ (589 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (57119 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (147 / 200 : ℝ) (589 / 800 : ℝ) (2174617 / 500000 : ℝ) (4360124024281 / 1000000000000 : ℝ)
    (151477161 / 100000000 : ℝ) (847 / 500000000 : ℝ) (57119 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (147 / 200 : ℝ)) (2174617 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (589 / 800 : ℝ) (2088091 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (589 / 800 : ℝ))) h 2
    have he :
        (Real.exp (589 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (589 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2174617 / 500000 : ℝ) - (589 / 800 : ℝ) / 2) / 32)
      (151477161 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_589 :
    ∀ u : ℝ, (589 / 800 : ℝ) ≤ u → u ≤ (59 / 80 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (222111 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (589 / 800 : ℝ) (59 / 80 : ℝ) (4360121 / 1000000 : ℝ) (4371039034209 / 1000000000000 : ℝ)
    (151636107 / 100000000 : ℝ) (16381 / 10000000000 : ℝ) (222111 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (589 / 800 : ℝ)) (4360121 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (59 / 80 : ℝ) (2090703 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (59 / 80 : ℝ))) h 2
    have he :
        (Real.exp (59 / 80 : ℝ)) ^ 2 =
          Real.exp (2 * (59 / 80 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4360121 / 1000000 : ℝ) - (59 / 80 : ℝ) / 2) / 32)
      (151636107 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_590 :
    ∀ u : ℝ, (59 / 80 : ℝ) ≤ u → u ≤ (591 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (6747 / 3125000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (59 / 80 : ℝ) (591 / 800 : ℝ) (874207 / 200000 : ℝ) (1095495062281 / 250000000000 : ℝ)
    (75897811 / 50000000 : ℝ) (15839 / 10000000000 : ℝ) (6747 / 3125000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (59 / 80 : ℝ)) (874207 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (591 / 800 : ℝ) (1046659 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (591 / 800 : ℝ))) h 2
    have he :
        (Real.exp (591 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (591 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (874207 / 200000 : ℝ) - (591 / 800 : ℝ) / 2) / 32)
      (75897811 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_591 :
    ∀ u : ℝ, (591 / 800 : ℝ) ≤ u → u ≤ (37 / 50 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (52461 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (591 / 800 : ℝ) (37 / 50 : ℝ) (547747 / 125000 : ℝ) (1072497001 / 244140625 : ℝ)
    (151955707 / 100000000 : ℝ) (15313 / 10000000000 : ℝ) (52461 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (591 / 800 : ℝ)) (547747 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (37 / 50 : ℝ) (32749 / 15625 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (37 / 50 : ℝ))) h 2
    have he :
        (Real.exp (37 / 50 : ℝ)) ^ 2 =
          Real.exp (2 * (37 / 50 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (547747 / 125000 : ℝ) - (37 / 50 : ℝ) / 2) / 32)
      (151955707 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_592 :
    ∀ u : ℝ, (37 / 50 : ℝ) ≤ u → u ≤ (593 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (203947 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (37 / 50 : ℝ) (593 / 800 : ℝ) (878589 / 200000 : ℝ) (1100986419841 / 250000000000 : ℝ)
    (152116379 / 100000000 : ℝ) (3701 / 2500000000 : ℝ) (203947 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (37 / 50 : ℝ)) (878589 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (593 / 800 : ℝ) (1049279 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (593 / 800 : ℝ))) h 2
    have he :
        (Real.exp (593 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (593 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (878589 / 200000 : ℝ) - (593 / 800 : ℝ) / 2) / 32)
      (152116379 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_593 :
    ∀ u : ℝ, (593 / 800 : ℝ) ≤ u → u ≤ (297 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (198203 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (593 / 800 : ℝ) (297 / 400 : ℝ) (4403941 / 1000000 : ℝ) (1103741449281 / 250000000000 : ℝ)
    (19034703 / 12500000 : ℝ) (14311 / 10000000000 : ℝ) (198203 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (593 / 800 : ℝ)) (4403941 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (297 / 400 : ℝ) (1050591 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (297 / 400 : ℝ))) h 2
    have he :
        (Real.exp (297 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (297 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4403941 / 1000000 : ℝ) - (297 / 400 : ℝ) / 2) / 32)
      (19034703 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_594 :
    ∀ u : ℝ, (297 / 400 : ℝ) ≤ u → u ≤ (119 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (192587 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (297 / 400 : ℝ) (119 / 160 : ℝ) (882993 / 200000 : ℝ) (4426020723721 / 1000000000000 : ℝ)
    (152439459 / 100000000 : ℝ) (1729 / 1250000000 : ℝ) (192587 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (297 / 400 : ℝ)) (882993 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (119 / 160 : ℝ) (2103811 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (119 / 160 : ℝ))) h 2
    have he :
        (Real.exp (119 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (119 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (882993 / 200000 : ℝ) - (119 / 160 : ℝ) / 2) / 32)
      (152439459 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_595 :
    ∀ u : ℝ, (119 / 160 : ℝ) ≤ u → u ≤ (149 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (18713 / 10000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (119 / 160 : ℝ) (149 / 200 : ℝ) (138313 / 31250 : ℝ) (1109274474841 / 250000000000 : ℝ)
    (152601871 / 100000000 : ℝ) (13369 / 10000000000 : ℝ) (18713 / 10000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (119 / 160 : ℝ)) (138313 / 31250 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (149 / 200 : ℝ) (1053221 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (149 / 200 : ℝ))) h 2
    have he :
        (Real.exp (149 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (149 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (138313 / 31250 : ℝ) - (149 / 200 : ℝ) / 2) / 32)
      (152601871 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_596 :
    ∀ u : ℝ, (149 / 200 : ℝ) ≤ u → u ≤ (597 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (90903 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (149 / 200 : ℝ) (597 / 800 : ℝ) (887419 / 200000 : ℝ) (4448205791929 / 1000000000000 : ℝ)
    (1222119 / 800000 : ℝ) (323 / 250000000 : ℝ) (90903 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (149 / 200 : ℝ)) (887419 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (597 / 800 : ℝ) (2109077 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (597 / 800 : ℝ))) h 2
    have he :
        (Real.exp (597 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (597 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (887419 / 200000 : ℝ) - (597 / 800 : ℝ) / 2) / 32)
      (1222119 / 800000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_597 :
    ∀ u : ℝ, (597 / 800 : ℝ) ≤ u → u ≤ (299 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (88309 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (597 / 800 : ℝ) (299 / 400 : ℝ) (4448201 / 1000000 : ℝ) (178373609649 / 40000000000 : ℝ)
    (76464229 / 50000000 : ℝ) (2497 / 2000000000 : ℝ) (88309 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (597 / 800 : ℝ)) (4448201 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (299 / 400 : ℝ) (422343 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (299 / 400 : ℝ))) h 2
    have he :
        (Real.exp (299 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (299 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (4448201 / 1000000 : ℝ) - (299 / 400 : ℝ) / 2) / 32)
      (76464229 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_598 :
    ∀ u : ℝ, (299 / 400 : ℝ) ≤ u → u ≤ (599 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (10723 / 6250000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (299 / 400 : ℝ) (599 / 800 : ℝ) (557417 / 125000 : ℝ) (279406330921 / 62500000000 : ℝ)
    (38273163 / 25000000 : ℝ) (377 / 312500000 : ℝ) (10723 / 6250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (299 / 400 : ℝ)) (557417 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (599 / 800 : ℝ) (528589 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (599 / 800 : ℝ))) h 2
    have he :
        (Real.exp (599 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (599 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (557417 / 125000 : ℝ) - (599 / 800 : ℝ) / 2) / 32)
      (38273163 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_599 :
    ∀ u : ℝ, (599 / 800 : ℝ) ≤ u → u ≤ (3 / 4 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (20829 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (599 / 800 : ℝ) (3 / 4 : ℝ) (2235249 / 500000 : ℝ) (4481693234001 / 1000000000000 : ℝ)
    (153257429 / 100000000 : ℝ) (2331 / 2000000000 : ℝ) (20829 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (599 / 800 : ℝ)) (2235249 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (3 / 4 : ℝ) (2117001 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (3 / 4 : ℝ))) h 2
    have he :
        (Real.exp (3 / 4 : ℝ)) ^ 2 =
          Real.exp (2 * (3 / 4 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (2235249 / 500000 : ℝ) - (3 / 4 : ℝ) / 2) / 32)
      (153257429 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_580
#print axioms hpThetaEnergyUpper_interval_599

end HodgeProofHP
