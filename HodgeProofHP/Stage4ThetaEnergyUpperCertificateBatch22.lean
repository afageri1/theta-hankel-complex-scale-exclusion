import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_440 :
    ∀ u : ℝ, (11 / 20 : ℝ) ≤ u → u ≤ (441 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (3207193 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (11 / 20 : ℝ) (441 / 800 : ℝ) (1502083 / 500000 : ℝ) (3011686047241 / 1000000000000 : ℝ)
    (133131943 / 100000000 : ℝ) (263577 / 2500000000 : ℝ) (3207193 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (11 / 20 : ℝ)) (1502083 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (441 / 800 : ℝ) (1735421 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (441 / 800 : ℝ))) h 2
    have he :
        (Real.exp (441 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (441 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1502083 / 500000 : ℝ) - (441 / 800 : ℝ) / 2) / 32)
      (133131943 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_441 :
    ∀ u : ℝ, (441 / 800 : ℝ) ≤ u → u ≤ (221 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (6303001 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (441 / 800 : ℝ) (221 / 400 : ℝ) (602337 / 200000 : ℝ) (47175405601 / 15625000000 : ℝ)
    (66613801 / 50000000 : ℝ) (64397 / 625000000 : ℝ) (6303001 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (441 / 800 : ℝ)) (602337 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (221 / 400 : ℝ) (217199 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (221 / 400 : ℝ))) h 2
    have he :
        (Real.exp (221 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (221 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (602337 / 200000 : ℝ) - (221 / 400 : ℝ) / 2) / 32)
      (66613801 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_442 :
    ∀ u : ℝ, (221 / 400 : ℝ) ≤ u → u ≤ (443 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (3096567 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (221 / 400 : ℝ) (443 / 800 : ℝ) (377403 / 125000 : ℝ) (121071290209 / 40000000000 : ℝ)
    (16665449 / 12500000 : ℝ) (251719 / 2500000000 : ℝ) (3096567 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (221 / 400 : ℝ)) (377403 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (443 / 800 : ℝ) (347953 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (443 / 800 : ℝ))) h 2
    have he :
        (Real.exp (443 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (443 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (377403 / 125000 : ℝ) - (443 / 800 : ℝ) / 2) / 32)
      (16665449 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_443 :
    ∀ u : ℝ, (443 / 800 : ℝ) ≤ u → u ≤ (111 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (6084839 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (443 / 800 : ℝ) (111 / 200 : ℝ) (3026781 / 1000000 : ℝ) (3034358447481 / 1000000000000 : ℝ)
    (66709943 / 50000000 : ℝ) (24597 / 250000000 : ℝ) (6084839 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (443 / 800 : ℝ)) (3026781 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (111 / 200 : ℝ) (1741941 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (111 / 200 : ℝ))) h 2
    have he :
        (Real.exp (111 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (111 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3026781 / 1000000 : ℝ) - (111 / 200 : ℝ) / 2) / 32)
      (66709943 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_444 :
    ∀ u : ℝ, (111 / 200 : ℝ) ≤ u → u ≤ (89 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (5978059 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (111 / 200 : ℝ) (89 / 160 : ℝ) (1517179 / 500000 : ℝ) (1901221609 / 625000000 : ℝ)
    (4172391 / 3125000 : ℝ) (961349 / 10000000000 : ℝ) (5978059 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (111 / 200 : ℝ)) (1517179 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (89 / 160 : ℝ) (43603 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (89 / 160 : ℝ))) h 2
    have he :
        (Real.exp (89 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (89 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1517179 / 500000 : ℝ) - (89 / 160 : ℝ) / 2) / 32)
      (4172391 / 3125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_445 :
    ∀ u : ℝ, (89 / 160 : ℝ) ≤ u → u ≤ (223 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1468203 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (89 / 160 : ℝ) (223 / 400 : ℝ) (3041953 / 1000000 : ℝ) (762392668801 / 250000000000 : ℝ)
    (33403361 / 25000000 : ℝ) (11741 / 125000000 : ℝ) (1468203 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (89 / 160 : ℝ)) (3041953 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (223 / 400 : ℝ) (873151 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (223 / 400 : ℝ))) h 2
    have he :
        (Real.exp (223 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (223 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3041953 / 1000000 : ℝ) - (223 / 400 : ℝ) / 2) / 32)
      (33403361 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_446 :
    ∀ u : ℝ, (223 / 400 : ℝ) ≤ u → u ≤ (447 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2884521 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (223 / 400 : ℝ) (447 / 800 : ℝ) (95299 / 31250 : ℝ) (764300823049 / 250000000000 : ℝ)
    (33427677 / 25000000 : ℝ) (917661 / 10000000000 : ℝ) (2884521 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (223 / 400 : ℝ)) (95299 / 31250 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (447 / 800 : ℝ) (874243 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (447 / 800 : ℝ))) h 2
    have he :
        (Real.exp (447 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (447 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (95299 / 31250 : ℝ) - (447 / 800 : ℝ) / 2) / 32)
      (33427677 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_447 :
    ∀ u : ℝ, (447 / 800 : ℝ) ≤ u → u ≤ (14 / 25 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (5666777 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (447 / 800 : ℝ) (14 / 25 : ℝ) (3057201 / 1000000 : ℝ) (3064855952929 / 1000000000000 : ℝ)
    (3345207 / 2500000 : ℝ) (112061 / 1250000000 : ℝ) (5666777 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (447 / 800 : ℝ)) (3057201 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (14 / 25 : ℝ) (1750673 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (14 / 25 : ℝ))) h 2
    have he :
        (Real.exp (14 / 25 : ℝ)) ^ 2 =
          Real.exp (2 * (14 / 25 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3057201 / 1000000 : ℝ) - (14 / 25 : ℝ) / 2) / 32)
      (3345207 / 2500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_448 :
    ∀ u : ℝ, (14 / 25 : ℝ) ≤ u → u ≤ (449 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2782987 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (14 / 25 : ℝ) (449 / 800 : ℝ) (1532427 / 500000 : ℝ) (3072528696769 / 1000000000000 : ℝ)
    (66953093 / 50000000 : ℝ) (875749 / 10000000000 : ℝ) (2782987 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (14 / 25 : ℝ)) (1532427 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (449 / 800 : ℝ) (1752863 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (449 / 800 : ℝ))) h 2
    have he :
        (Real.exp (449 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (449 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1532427 / 500000 : ℝ) - (449 / 800 : ℝ) / 2) / 32)
      (66953093 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_449 :
    ∀ u : ℝ, (449 / 800 : ℝ) ≤ u → u ≤ (9 / 16 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (5466641 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (449 / 800 : ℝ) (9 / 16 : ℝ) (122901 / 40000 : ℝ) (123208722121 / 40000000000 : ℝ)
    (335011 / 250000 : ℝ) (427721 / 5000000000 : ℝ) (5466641 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (449 / 800 : ℝ)) (122901 / 40000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (9 / 16 : ℝ) (351011 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (9 / 16 : ℝ))) h 2
    have he :
        (Real.exp (9 / 16 : ℝ)) ^ 2 =
          Real.exp (2 * (9 / 16 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (122901 / 40000 : ℝ) - (9 / 16 : ℝ) / 2) / 32)
      (335011 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_450 :
    ∀ u : ℝ, (9 / 16 : ℝ) ≤ u → u ≤ (451 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2684369 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (9 / 16 : ℝ) (451 / 800 : ℝ) (385027 / 125000 : ℝ) (49406841 / 16000000 : ℝ)
    (134102949 / 100000000 : ℝ) (835553 / 10000000000 : ℝ) (2684369 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (9 / 16 : ℝ)) (385027 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (451 / 800 : ℝ) (7029 / 4000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (451 / 800 : ℝ))) h 2
    have he :
        (Real.exp (451 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (451 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (385027 / 125000 : ℝ) - (451 / 800 : ℝ) / 2) / 32)
      (134102949 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_451 :
    ∀ u : ℝ, (451 / 800 : ℝ) ≤ u → u ≤ (113 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1318063 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (451 / 800 : ℝ) (113 / 200 : ℝ) (3087927 / 1000000 : ℝ) (48369644761 / 15625000000 : ℝ)
    (67100917 / 50000000 : ℝ) (32643 / 400000000 : ℝ) (1318063 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (451 / 800 : ℝ)) (3087927 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (113 / 200 : ℝ) (219931 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (113 / 200 : ℝ))) h 2
    have he :
        (Real.exp (113 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (113 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3087927 / 1000000 : ℝ) - (113 / 200 : ℝ) / 2) / 32)
      (67100917 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_452 :
    ∀ u : ℝ, (113 / 200 : ℝ) ≤ u → u ≤ (453 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (5177197 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (113 / 200 : ℝ) (453 / 800 : ℝ) (386957 / 125000 : ℝ) (3103407199201 / 1000000000000 : ℝ)
    (13430103 / 10000000 : ℝ) (159401 / 2000000000 : ℝ) (5177197 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (113 / 200 : ℝ)) (386957 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (453 / 800 : ℝ) (1761649 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (453 / 800 : ℝ))) h 2
    have he :
        (Real.exp (453 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (453 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (386957 / 125000 : ℝ) - (453 / 800 : ℝ) / 2) / 32)
      (13430103 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_453 :
    ∀ u : ℝ, (453 / 800 : ℝ) ≤ u → u ≤ (227 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (5083529 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (453 / 800 : ℝ) (227 / 400 : ℝ) (620681 / 200000 : ℝ) (194448367369 / 62500000000 : ℝ)
    (67200281 / 50000000 : ℝ) (778333 / 10000000000 : ℝ) (5083529 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (453 / 800 : ℝ)) (620681 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (227 / 400 : ℝ) (440963 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (227 / 400 : ℝ))) h 2
    have he :
        (Real.exp (227 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (227 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (620681 / 200000 : ℝ) - (227 / 400 : ℝ) / 2) / 32)
      (67200281 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_454 :
    ∀ u : ℝ, (227 / 400 : ℝ) ≤ u → u ≤ (91 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2495633 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (227 / 400 : ℝ) (91 / 160 : ℝ) (3111173 / 1000000 : ℝ) (3118964391481 / 1000000000000 : ℝ)
    (134500419 / 100000000 : ℝ) (760053 / 10000000000 : ℝ) (2495633 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (227 / 400 : ℝ)) (3111173 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (91 / 160 : ℝ) (1766059 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (91 / 160 : ℝ))) h 2
    have he :
        (Real.exp (91 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (91 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3111173 / 1000000 : ℝ) - (91 / 160 : ℝ) / 2) / 32)
      (134500419 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_455 :
    ∀ u : ℝ, (91 / 160 : ℝ) ≤ u → u ≤ (57 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1225089 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (91 / 160 : ℝ) (57 / 100 : ℝ) (3118961 / 1000000 : ℝ) (195423232489 / 62500000000 : ℝ)
    (67300307 / 50000000 : ℝ) (185539 / 2500000000 : ℝ) (1225089 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (91 / 160 : ℝ)) (3118961 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (57 / 100 : ℝ) (442067 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (57 / 100 : ℝ))) h 2
    have he :
        (Real.exp (57 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (57 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3118961 / 1000000 : ℝ) - (57 / 100 : ℝ) / 2) / 32)
      (67300307 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_456 :
    ∀ u : ℝ, (57 / 100 : ℝ) ≤ u → u ≤ (457 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (481079 / 10000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (57 / 100 : ℝ) (457 / 800 : ℝ) (195423 / 62500 : ℝ) (3134595889441 / 1000000000000 : ℝ)
    (26940227 / 20000000 : ℝ) (181159 / 2500000000 : ℝ) (481079 / 10000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (57 / 100 : ℝ)) (195423 / 62500 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (457 / 800 : ℝ) (1770479 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (457 / 800 : ℝ))) h 2
    have he :
        (Real.exp (457 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (457 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (195423 / 62500 : ℝ) - (457 / 800 : ℝ) / 2) / 32)
      (26940227 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_457 :
    ∀ u : ℝ, (457 / 800 : ℝ) ≤ u → u ≤ (229 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (236129 / 5000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (457 / 800 : ℝ) (229 / 400 : ℝ) (626919 / 200000 : ℝ) (785611004409 / 250000000000 : ℝ)
    (33700499 / 25000000 : ℝ) (353743 / 5000000000 : ℝ) (236129 / 5000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (457 / 800 : ℝ)) (626919 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (229 / 400 : ℝ) (886347 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (229 / 400 : ℝ))) h 2
    have he :
        (Real.exp (229 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (229 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (626919 / 200000 : ℝ) - (229 / 400 : ℝ) / 2) / 32)
      (33700499 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_458 :
    ∀ u : ℝ, (229 / 400 : ℝ) ≤ u → u ≤ (459 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2317849 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (229 / 400 : ℝ) (459 / 800 : ℝ) (3142441 / 1000000 : ℝ) (3150309057921 / 1000000000000 : ℝ)
    (134903183 / 100000000 : ℝ) (690701 / 10000000000 : ℝ) (2317849 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (229 / 400 : ℝ)) (3142441 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (459 / 800 : ℝ) (1774911 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (459 / 800 : ℝ))) h 2
    have he :
        (Real.exp (459 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (459 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3142441 / 1000000 : ℝ) - (459 / 800 : ℝ) / 2) / 32)
      (134903183 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_459 :
    ∀ u : ℝ, (459 / 800 : ℝ) ≤ u → u ≤ (23 / 40 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (4550119 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (459 / 800 : ℝ) (23 / 40 : ℝ) (3150307 / 1000000 : ℝ) (3158194591161 / 1000000000000 : ℝ)
    (16875589 / 12500000 : ℝ) (674271 / 10000000000 : ℝ) (4550119 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (459 / 800 : ℝ)) (3150307 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (23 / 40 : ℝ) (1777131 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (23 / 40 : ℝ))) h 2
    have he :
        (Real.exp (23 / 40 : ℝ)) ^ 2 =
          Real.exp (2 * (23 / 40 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3150307 / 1000000 : ℝ) - (23 / 40 : ℝ) / 2) / 32)
      (16875589 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_440
#print axioms hpThetaEnergyUpper_interval_459

end HodgeProofHP
