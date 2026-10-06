import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_80 :
    ∀ u : ℝ, (1 / 10 : ℝ) ≤ u → u ≤ (81 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (83132271 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (1 / 10 : ℝ) (81 / 800 : ℝ) (610701 / 500000 : ℝ) (306115438729 / 250000000000 : ℝ)
    (7034661 / 6250000 : ℝ) (113592329 / 5000000000 : ℝ) (83132271 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (1 / 10 : ℝ)) (610701 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (81 / 800 : ℝ) (553277 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (81 / 800 : ℝ))) h 2
    have he :
        (Real.exp (81 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (81 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (610701 / 500000 : ℝ) - (81 / 800 : ℝ) / 2) / 32)
      (7034661 / 6250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_81 :
    ∀ u : ℝ, (81 / 800 : ℝ) ≤ u → u ≤ (41 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (41466299 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (81 / 800 : ℝ) (41 / 400 : ℝ) (61223 / 50000 : ℝ) (306881652961 / 250000000000 : ℝ)
    (28146539 / 25000000 : ℝ) (56288579 / 2500000000 : ℝ) (41466299 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (81 / 800 : ℝ)) (61223 / 50000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (41 / 400 : ℝ) (553969 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (41 / 400 : ℝ))) h 2
    have he :
        (Real.exp (41 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (41 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (61223 / 50000 : ℝ) - (41 / 400 : ℝ) / 2) / 32)
      (28146539 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_82 :
    ∀ u : ℝ, (41 / 400 : ℝ) ≤ u → u ≤ (83 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (82731221 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (41 / 400 : ℝ) (83 / 800 : ℝ) (49101 / 40000 : ℝ) (76912483561 / 62500000000 : ℝ)
    (56308911 / 50000000 : ℝ) (223137229 / 10000000000 : ℝ) (82731221 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (41 / 400 : ℝ)) (49101 / 40000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (83 / 800 : ℝ) (277331 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (83 / 800 : ℝ))) h 2
    have he :
        (Real.exp (83 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (83 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (49101 / 40000 : ℝ) - (83 / 800 : ℝ) / 2) / 32)
      (56308911 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_83 :
    ∀ u : ℝ, (83 / 800 : ℝ) ≤ u → u ≤ (21 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (165055351 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (83 / 800 : ℝ) (21 / 200 : ℝ) (1230597 / 1000000 : ℝ) (1233678925521 / 1000000000000 : ℝ)
    (56324787 / 50000000 : ℝ) (221133369 / 10000000000 : ℝ) (165055351 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (83 / 800 : ℝ)) (1230597 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (21 / 200 : ℝ) (1110711 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (21 / 200 : ℝ))) h 2
    have he :
        (Real.exp (21 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (21 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1230597 / 1000000 : ℝ) - (21 / 200 : ℝ) / 2) / 32)
      (56324787 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_84 :
    ∀ u : ℝ, (21 / 200 : ℝ) ≤ u → u ≤ (17 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (16464369 / 10000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (21 / 200 : ℝ) (17 / 160 : ℝ) (616839 / 500000 : ℝ) (123676641 / 100000000 : ℝ)
    (22536287 / 20000000 : ℝ) (109570639 / 5000000000 : ℝ) (16464369 / 10000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (21 / 200 : ℝ)) (616839 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (17 / 160 : ℝ) (11121 / 10000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (17 / 160 : ℝ))) h 2
    have he :
        (Real.exp (17 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (17 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (616839 / 500000 : ℝ) - (17 / 160 : ℝ) / 2) / 32)
      (22536287 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_85 :
    ∀ u : ℝ, (17 / 160 : ℝ) ≤ u → u ≤ (43 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (32845749 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (17 / 160 : ℝ) (43 / 400 : ℝ) (618383 / 500000 : ℝ) (1239862207081 / 1000000000000 : ℝ)
    (56356691 / 50000000 : ℝ) (108581193 / 5000000000 : ℝ) (32845749 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (17 / 160 : ℝ)) (618383 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (43 / 400 : ℝ) (1113491 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (43 / 400 : ℝ))) h 2
    have he :
        (Real.exp (43 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (43 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (618383 / 500000 : ℝ) - (43 / 400 : ℝ) / 2) / 32)
      (56356691 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_86 :
    ∀ u : ℝ, (43 / 400 : ℝ) ≤ u → u ≤ (87 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (81905253 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (43 / 400 : ℝ) (87 / 800 : ℝ) (1239861 / 1000000 : ℝ) (77685395841 / 62500000000 : ℝ)
    (14093177 / 12500000 : ℝ) (53799151 / 2500000000 : ℝ) (81905253 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (43 / 400 : ℝ)) (1239861 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (87 / 800 : ℝ) (278721 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (87 / 800 : ℝ))) h 2
    have he :
        (Real.exp (87 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (87 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1239861 / 1000000 : ℝ) - (87 / 800 : ℝ) / 2) / 32)
      (14093177 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_87 :
    ∀ u : ℝ, (87 / 800 : ℝ) ≤ u → u ≤ (11 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (6535513 / 4000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (87 / 800 : ℝ) (11 / 100 : ℝ) (248593 / 200000 : ℝ) (1246078805841 / 1000000000000 : ℝ)
    (112777559 / 100000000 : ℝ) (213242571 / 10000000000 : ℝ) (6535513 / 4000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (87 / 800 : ℝ)) (248593 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (11 / 100 : ℝ) (1116279 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (11 / 100 : ℝ))) h 2
    have he :
        (Real.exp (11 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (11 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (248593 / 200000 : ℝ) - (11 / 100 : ℝ) / 2) / 32)
      (112777559 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_88 :
    ∀ u : ℝ, (11 / 100 : ℝ) ≤ u → u ≤ (89 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (162961037 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (11 / 100 : ℝ) (89 / 800 : ℝ) (311519 / 250000 : ℝ) (1998715849 / 1600000000 : ℝ)
    (28202447 / 25000000 : ℝ) (52825419 / 2500000000 : ℝ) (162961037 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (11 / 100 : ℝ)) (311519 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (89 / 800 : ℝ) (44707 / 40000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (89 / 800 : ℝ))) h 2
    have he :
        (Real.exp (89 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (89 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (311519 / 250000 : ℝ) - (89 / 800 : ℝ) / 2) / 32)
      (28202447 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_89 :
    ∀ u : ℝ, (89 / 800 : ℝ) ≤ u → u ≤ (9 / 80 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (162530493 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (89 / 800 : ℝ) (9 / 80 : ℝ) (249839 / 200000 : ℝ) (1252324379329 / 1000000000000 : ℝ)
    (22568423 / 20000000 : ℝ) (8374927 / 400000000 : ℝ) (162530493 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (89 / 800 : ℝ)) (249839 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (9 / 80 : ℝ) (1119073 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (9 / 80 : ℝ))) h 2
    have he :
        (Real.exp (9 / 80 : ℝ)) ^ 2 =
          Real.exp (2 * (9 / 80 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (249839 / 200000 : ℝ) - (9 / 80 : ℝ) / 2) / 32)
      (22568423 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_90 :
    ∀ u : ℝ, (9 / 80 : ℝ) ≤ u → u ≤ (91 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (162095309 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (9 / 80 : ℝ) (91 / 800 : ℝ) (626161 / 500000 : ℝ) (19616523481 / 15625000000 : ℝ)
    (5643727 / 5000000 : ℝ) (6483033 / 312500000 : ℝ) (162095309 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (9 / 80 : ℝ)) (626161 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (91 / 800 : ℝ) (140059 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (91 / 800 : ℝ))) h 2
    have he :
        (Real.exp (91 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (91 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (626161 / 500000 : ℝ) - (91 / 800 : ℝ) / 2) / 32)
      (5643727 / 5000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_91 :
    ∀ u : ℝ, (91 / 800 : ℝ) ≤ u → u ≤ (23 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (40414347 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (91 / 800 : ℝ) (23 / 200 : ℝ) (1255457 / 1000000 : ℝ) (314650317969 / 250000000000 : ℝ)
    (112907063 / 100000000 : ℝ) (102776653 / 5000000000 : ℝ) (40414347 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (91 / 800 : ℝ)) (1255457 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (23 / 200 : ℝ) (560937 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (23 / 200 : ℝ))) h 2
    have he :
        (Real.exp (23 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (23 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1255457 / 1000000 : ℝ) - (23 / 200 : ℝ) / 2) / 32)
      (112907063 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_92 :
    ∀ u : ℝ, (23 / 200 : ℝ) ≤ u → u ≤ (93 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (20151871 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (23 / 200 : ℝ) (93 / 800 : ℝ) (6293 / 5000 : ℝ) (1261751218729 / 1000000000000 : ℝ)
    (112939683 / 100000000 : ℝ) (20366197 / 1000000000 : ℝ) (20151871 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (23 / 200 : ℝ)) (6293 / 5000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (93 / 800 : ℝ) (1123277 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (93 / 800 : ℝ))) h 2
    have he :
        (Real.exp (93 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (93 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (6293 / 5000 : ℝ) - (93 / 800 : ℝ) / 2) / 32)
      (112939683 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_93 :
    ∀ u : ℝ, (93 / 800 : ℝ) ≤ u → u ≤ (47 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (5024047 / 3125000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (93 / 800 : ℝ) (47 / 400 : ℝ) (5047 / 4000 : ℝ) (316227400281 / 250000000000 : ℝ)
    (112972391 / 100000000 : ℝ) (25222943 / 1250000000 : ℝ) (5024047 / 3125000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (93 / 800 : ℝ)) (5047 / 4000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (47 / 400 : ℝ) (562341 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (47 / 400 : ℝ))) h 2
    have he :
        (Real.exp (47 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (47 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (5047 / 4000 : ℝ) - (47 / 400 : ℝ) / 2) / 32)
      (112972391 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_94 :
    ∀ u : ℝ, (47 / 400 : ℝ) ≤ u → u ≤ (19 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (160320507 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (47 / 400 : ℝ) (19 / 160 : ℝ) (316227 / 250000 : ℝ) (1268076435921 / 1000000000000 : ℝ)
    (113005197 / 100000000 : ℝ) (199917433 / 10000000000 : ℝ) (160320507 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (47 / 400 : ℝ)) (316227 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (19 / 160 : ℝ) (1126089 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (19 / 160 : ℝ))) h 2
    have he :
        (Real.exp (19 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (19 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (316227 / 250000 : ℝ) - (19 / 160 : ℝ) / 2) / 32)
      (113005197 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_95 :
    ∀ u : ℝ, (19 / 160 : ℝ) ≤ u → u ≤ (3 / 25 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (79933557 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (19 / 160 : ℝ) (3 / 25 : ℝ) (634037 / 500000 : ℝ) (1271249485009 / 1000000000000 : ℝ)
    (113038101 / 100000000 : ℝ) (99031809 / 5000000000 : ℝ) (79933557 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (19 / 160 : ℝ)) (634037 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (3 / 25 : ℝ) (1127497 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (3 / 25 : ℝ))) h 2
    have he :
        (Real.exp (3 / 25 : ℝ)) ^ 2 =
          Real.exp (2 * (3 / 25 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (634037 / 500000 : ℝ) - (3 / 25 : ℝ) / 2) / 32)
      (113038101 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_96 :
    ∀ u : ℝ, (3 / 25 : ℝ) ≤ u → u ≤ (97 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (31882113 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (3 / 25 : ℝ) (97 / 800 : ℝ) (1271249 / 1000000 : ℝ) (79652079529 / 62500000000 : ℝ)
    (22614223 / 20000000 : ℝ) (196221417 / 10000000000 : ℝ) (31882113 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (3 / 25 : ℝ)) (1271249 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (97 / 800 : ℝ) (282227 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (97 / 800 : ℝ))) h 2
    have he :
        (Real.exp (97 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (97 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1271249 / 1000000 : ℝ) - (97 / 800 : ℝ) / 2) / 32)
      (22614223 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_97 :
    ∀ u : ℝ, (97 / 800 : ℝ) ≤ u → u ≤ (49 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (158950291 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (97 / 800 : ℝ) (49 / 400 : ℝ) (1274431 / 1000000 : ℝ) (199628641 / 156250000 : ℝ)
    (14138027 / 12500000 : ℝ) (6074753 / 312500000 : ℝ) (158950291 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (97 / 800 : ℝ)) (1274431 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (49 / 400 : ℝ) (14129 / 12500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (49 / 400 : ℝ))) h 2
    have he :
        (Real.exp (49 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (49 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1274431 / 1000000 : ℝ) - (49 / 400 : ℝ) / 2) / 32)
      (14138027 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_98 :
    ∀ u : ℝ, (49 / 400 : ℝ) ≤ u → u ≤ (99 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (158485733 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (49 / 400 : ℝ) (99 / 800 : ℝ) (1277621 / 1000000 : ℝ) (1280819583289 / 1000000000000 : ℝ)
    (14142177 / 12500000 : ℝ) (38514993 / 2000000000 : ℝ) (158485733 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (49 / 400 : ℝ)) (1277621 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (99 / 800 : ℝ) (1131733 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (99 / 800 : ℝ))) h 2
    have he :
        (Real.exp (99 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (99 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1277621 / 1000000 : ℝ) - (99 / 800 : ℝ) / 2) / 32)
      (14142177 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_99 :
    ∀ u : ℝ, (99 / 800 : ℝ) ≤ u → u ≤ (1 / 8 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (3950469 / 2500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (99 / 800 : ℝ) (1 / 8 : ℝ) (1280819 / 1000000 : ℝ) (1284026656201 / 1000000000000 : ℝ)
    (56585357 / 50000000 : ℝ) (190770059 / 10000000000 : ℝ) (3950469 / 2500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (99 / 800 : ℝ)) (1280819 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (1 / 8 : ℝ) (1133149 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (1 / 8 : ℝ))) h 2
    have he :
        (Real.exp (1 / 8 : ℝ)) ^ 2 =
          Real.exp (2 * (1 / 8 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1280819 / 1000000 : ℝ) - (1 / 8 : ℝ) / 2) / 32)
      (56585357 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_80
#print axioms hpThetaEnergyUpper_interval_99

end HodgeProofHP
