import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_480 :
    ∀ u : ℝ, (3 / 5 : ℝ) ≤ u → u ≤ (481 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (6063 / 200000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (3 / 5 : ℝ) (481 / 800 : ℝ) (830029 / 250000 : ℝ) (832107015601 / 250000000000 : ℝ)
    (137216783 / 100000000 : ℝ) (200419 / 5000000000 : ℝ) (6063 / 200000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (3 / 5 : ℝ)) (830029 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (481 / 800 : ℝ) (912199 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (481 / 800 : ℝ))) h 2
    have he :
        (Real.exp (481 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (481 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (830029 / 250000 : ℝ) - (481 / 800 : ℝ) / 2) / 32)
      (137216783 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_481 :
    ∀ u : ℝ, (481 / 800 : ℝ) ≤ u → u ≤ (241 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2971303 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (481 / 800 : ℝ) (241 / 400 : ℝ) (3328427 / 1000000 : ℝ) (2085474889 / 625000000 : ℝ)
    (137326049 / 100000000 : ℝ) (390757 / 10000000000 : ℝ) (2971303 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (481 / 800 : ℝ)) (3328427 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (241 / 400 : ℝ) (45667 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (241 / 400 : ℝ))) h 2
    have he :
        (Real.exp (241 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (241 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3328427 / 1000000 : ℝ) - (241 / 400 : ℝ) / 2) / 32)
      (137326049 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_482 :
    ∀ u : ℝ, (241 / 400 : ℝ) ≤ u → u ≤ (483 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (291211 / 10000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (241 / 400 : ℝ) (483 / 800 : ℝ) (3336759 / 1000000 : ℝ) (133804518849 / 40000000000 : ℝ)
    (27487137 / 20000000 : ℝ) (76181 / 2000000000 : ℝ) (291211 / 10000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (241 / 400 : ℝ)) (3336759 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (483 / 800 : ℝ) (365793 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (483 / 800 : ℝ))) h 2
    have he :
        (Real.exp (483 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (483 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3336759 / 1000000 : ℝ) - (483 / 800 : ℝ) / 2) / 32)
      (27487137 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_483 :
    ∀ u : ℝ, (483 / 800 : ℝ) ≤ u → u ≤ (121 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2853907 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (483 / 800 : ℝ) (121 / 200 : ℝ) (3345111 / 1000000 : ℝ) (3353487550009 / 1000000000000 : ℝ)
    (137545679 / 100000000 : ℝ) (371277 / 10000000000 : ℝ) (2853907 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (483 / 800 : ℝ)) (3345111 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (121 / 200 : ℝ) (1831253 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (121 / 200 : ℝ))) h 2
    have he :
        (Real.exp (121 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (121 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3345111 / 1000000 : ℝ) - (121 / 200 : ℝ) / 2) / 32)
      (137545679 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_484 :
    ∀ u : ℝ, (121 / 200 : ℝ) ≤ u → u ≤ (97 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2796677 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (121 / 200 : ℝ) (97 / 160 : ℝ) (838371 / 250000 : ℝ) (3361879932849 / 1000000000000 : ℝ)
    (27531209 / 20000000 : ℝ) (361869 / 10000000000 : ℝ) (2796677 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (121 / 200 : ℝ)) (838371 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (97 / 160 : ℝ) (1833543 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (97 / 160 : ℝ))) h 2
    have he :
        (Real.exp (97 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (97 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (838371 / 250000 : ℝ) - (97 / 160 : ℝ) / 2) / 32)
      (27531209 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_485 :
    ∀ u : ℝ, (97 / 160 : ℝ) ≤ u → u ≤ (243 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1370209 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (97 / 160 : ℝ) (243 / 400 : ℝ) (1680939 / 500000 : ℝ) (3370297490569 / 1000000000000 : ℝ)
    (68883391 / 50000000 : ℝ) (88169 / 2500000000 : ℝ) (1370209 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (97 / 160 : ℝ)) (1680939 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (243 / 400 : ℝ) (1835837 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (243 / 400 : ℝ))) h 2
    have he :
        (Real.exp (243 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (243 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1680939 / 500000 : ℝ) - (243 / 400 : ℝ) / 2) / 32)
      (68883391 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_486 :
    ∀ u : ℝ, (243 / 400 : ℝ) ≤ u → u ≤ (487 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2685097 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (243 / 400 : ℝ) (487 / 800 : ℝ) (1685147 / 500000 : ℝ) (3378732925689 / 1000000000000 : ℝ)
    (137877907 / 100000000 : ℝ) (343693 / 10000000000 : ℝ) (2685097 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (243 / 400 : ℝ)) (1685147 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (487 / 800 : ℝ) (1838133 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (487 / 800 : ℝ))) h 2
    have he :
        (Real.exp (487 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (487 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1685147 / 500000 : ℝ) - (487 / 800 : ℝ) / 2) / 32)
      (137877907 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_487 :
    ∀ u : ℝ, (487 / 800 : ℝ) ≤ u → u ≤ (61 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2630727 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (487 / 800 : ℝ) (61 / 100 : ℝ) (337873 / 100000 : ℝ) (13231210729 / 3906250000 : ℝ)
    (8624337 / 6250000 : ℝ) (167459 / 5000000000 : ℝ) (2630727 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (487 / 800 : ℝ)) (337873 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (61 / 100 : ℝ) (115027 / 62500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (61 / 100 : ℝ))) h 2
    have he :
        (Real.exp (61 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (61 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (337873 / 100000 : ℝ) - (61 / 100 : ℝ) / 2) / 32)
      (8624337 / 6250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_488 :
    ∀ u : ℝ, (61 / 100 : ℝ) ≤ u → u ≤ (489 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1288641 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (61 / 100 : ℝ) (489 / 800 : ℝ) (3387187 / 1000000 : ℝ) (848917148689 / 250000000000 : ℝ)
    (34525313 / 25000000 : ℝ) (65269 / 2000000000 : ℝ) (1288641 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (61 / 100 : ℝ)) (3387187 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (489 / 800 : ℝ) (921367 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (489 / 800 : ℝ))) h 2
    have he :
        (Real.exp (489 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (489 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3387187 / 1000000 : ℝ) - (489 / 800 : ℝ) / 2) / 32)
      (34525313 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_489 :
    ∀ u : ℝ, (489 / 800 : ℝ) ≤ u → u ≤ (49 / 80 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (10099 / 400000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (489 / 800 : ℝ) (49 / 80 : ℝ) (1697833 / 500000 : ℝ) (3404168911521 / 1000000000000 : ℝ)
    (138213501 / 100000000 : ℝ) (31797 / 1000000000 : ℝ) (10099 / 400000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (489 / 800 : ℝ)) (1697833 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (49 / 80 : ℝ) (1845039 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (49 / 80 : ℝ))) h 2
    have he :
        (Real.exp (49 / 80 : ℝ)) ^ 2 =
          Real.exp (2 * (49 / 80 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1697833 / 500000 : ℝ) - (49 / 80 : ℝ) / 2) / 32)
      (138213501 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_490 :
    ∀ u : ℝ, (49 / 80 : ℝ) ≤ u → u ≤ (491 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1236557 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (49 / 80 : ℝ) (491 / 800 : ℝ) (1702083 / 500000 : ℝ) (853171810929 / 250000000000 : ℝ)
    (69163063 / 50000000 : ℝ) (309789 / 10000000000 : ℝ) (1236557 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (49 / 80 : ℝ)) (1702083 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (491 / 800 : ℝ) (923673 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (491 / 800 : ℝ))) h 2
    have he :
        (Real.exp (491 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (491 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1702083 / 500000 : ℝ) - (491 / 800 : ℝ) / 2) / 32)
      (69163063 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_491 :
    ∀ u : ℝ, (491 / 800 : ℝ) ≤ u → u ≤ (123 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2422381 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (491 / 800 : ℝ) (123 / 200 : ℝ) (3412687 / 1000000 : ℝ) (3421231017649 / 1000000000000 : ℝ)
    (17304891 / 12500000 : ℝ) (301799 / 10000000000 : ℝ) (2422381 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (491 / 800 : ℝ)) (3412687 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (123 / 200 : ℝ) (1849657 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (123 / 200 : ℝ))) h 2
    have he :
        (Real.exp (123 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (123 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3412687 / 1000000 : ℝ) - (123 / 200 : ℝ) / 2) / 32)
      (17304891 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_492 :
    ∀ u : ℝ, (123 / 200 : ℝ) ≤ u → u ≤ (493 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (94901 / 4000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (123 / 200 : ℝ) (493 / 800 : ℝ) (3421229 / 1000000 : ℝ) (3429796584841 / 1000000000000 : ℝ)
    (34638127 / 25000000 : ℝ) (58799 / 2000000000 : ℝ) (94901 / 4000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (123 / 200 : ℝ)) (3421229 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (493 / 800 : ℝ) (1851971 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (493 / 800 : ℝ))) h 2
    have he :
        (Real.exp (493 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (493 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3421229 / 1000000 : ℝ) - (493 / 800 : ℝ) / 2) / 32)
      (34638127 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_493 :
    ∀ u : ℝ, (493 / 800 : ℝ) ≤ u → u ≤ (247 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1161767 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (493 / 800 : ℝ) (247 / 400 : ℝ) (3429793 / 1000000 : ℝ) (3438380278369 / 1000000000000 : ℝ)
    (3466657 / 2500000 : ℝ) (143187 / 5000000000 : ℝ) (1161767 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (493 / 800 : ℝ)) (3429793 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (247 / 400 : ℝ) (1854287 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (247 / 400 : ℝ))) h 2
    have he :
        (Real.exp (247 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (247 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3429793 / 1000000 : ℝ) - (247 / 400 : ℝ) / 2) / 32)
      (3466657 / 2500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_494 :
    ∀ u : ℝ, (247 / 400 : ℝ) ≤ u → u ≤ (99 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (1137697 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (247 / 400 : ℝ) (99 / 160 : ℝ) (1719189 / 500000 : ℝ) (861746459809 / 250000000000 : ℝ)
    (8673777 / 6250000 : ℝ) (278931 / 10000000000 : ℝ) (1137697 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (247 / 400 : ℝ)) (1719189 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (99 / 160 : ℝ) (928303 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (99 / 160 : ℝ))) h 2
    have he :
        (Real.exp (99 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (99 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1719189 / 500000 : ℝ) - (99 / 160 : ℝ) / 2) / 32)
      (8673777 / 6250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_495 :
    ∀ u : ℝ, (99 / 160 : ℝ) ≤ u → u ≤ (31 / 50 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2228111 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (99 / 160 : ℝ) (31 / 50 : ℝ) (689397 / 200000 : ℝ) (3455617027041 / 1000000000000 : ℝ)
    (138894977 / 100000000 : ℝ) (16979 / 625000000 : ℝ) (2228111 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (99 / 160 : ℝ)) (689397 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (31 / 50 : ℝ) (1858929 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (31 / 50 : ℝ))) h 2
    have he :
        (Real.exp (31 / 50 : ℝ)) ^ 2 =
          Real.exp (2 * (31 / 50 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (689397 / 200000 : ℝ) - (31 / 50 : ℝ) / 2) / 32)
      (138894977 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_496 :
    ∀ u : ℝ, (31 / 50 : ℝ) ≤ u → u ≤ (497 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (545413 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (31 / 50 : ℝ) (497 / 800 : ℝ) (3455613 / 1000000 : ℝ) (866066613129 / 250000000000 : ℝ)
    (139009903 / 100000000 : ℝ) (33071 / 1250000000 : ℝ) (545413 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (31 / 50 : ℝ)) (3455613 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (497 / 800 : ℝ) (930627 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (497 / 800 : ℝ))) h 2
    have he :
        (Real.exp (497 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (497 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3455613 / 1000000 : ℝ) - (497 / 800 : ℝ) / 2) / 32)
      (139009903 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_497 :
    ∀ u : ℝ, (497 / 800 : ℝ) ≤ u → u ≤ (249 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (133501 / 6250000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (497 / 800 : ℝ) (249 / 400 : ℝ) (3464263 / 1000000 : ℝ) (868234467681 / 250000000000 : ℝ)
    (5565009 / 4000000 : ℝ) (6441 / 250000000 : ℝ) (133501 / 6250000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (497 / 800 : ℝ)) (3464263 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (249 / 400 : ℝ) (931791 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (249 / 400 : ℝ))) h 2
    have he :
        (Real.exp (249 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (249 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3464263 / 1000000 : ℝ) - (249 / 400 : ℝ) / 2) / 32)
      (5565009 / 4000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_498 :
    ∀ u : ℝ, (249 / 400 : ℝ) ≤ u → u ≤ (499 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (522797 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (249 / 400 : ℝ) (499 / 800 : ℝ) (1736467 / 500000 : ℝ) (3481631323569 / 1000000000000 : ℝ)
    (139240929 / 100000000 : ℝ) (62719 / 2500000000 : ℝ) (522797 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (249 / 400 : ℝ)) (1736467 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (499 / 800 : ℝ) (1865913 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (499 / 800 : ℝ))) h 2
    have he :
        (Real.exp (499 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (499 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1736467 / 500000 : ℝ) - (499 / 800 : ℝ) / 2) / 32)
      (139240929 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_499 :
    ∀ u : ℝ, (499 / 800 : ℝ) ≤ u → u ≤ (5 / 8 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (2047163 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (499 / 800 : ℝ) (5 / 8 : ℝ) (3481627 / 1000000 : ℝ) (872585779129 / 250000000000 : ℝ)
    (139357031 / 100000000 : ℝ) (122137 / 5000000000 : ℝ) (2047163 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (499 / 800 : ℝ)) (3481627 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (5 / 8 : ℝ) (934123 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (5 / 8 : ℝ))) h 2
    have he :
        (Real.exp (5 / 8 : ℝ)) ^ 2 =
          Real.exp (2 * (5 / 8 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (3481627 / 1000000 : ℝ) - (5 / 8 : ℝ) / 2) / 32)
      (139357031 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_480
#print axioms hpThetaEnergyUpper_interval_499

end HodgeProofHP
