import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_0 :
    ∀ u : ℝ, (0 / 1 : ℝ) ≤ u → u ≤ (1 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (182805893 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (0 / 1 : ℝ) (1 / 800 : ℝ) (1 / 1 : ℝ) (1002503565001 / 1000000000000 : ℝ)
    (110307911 / 100000000 : ℝ) (433098699 / 10000000000 : ℝ) (182805893 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (0 / 1 : ℝ)) (1 / 1 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (1 / 800 : ℝ) (1001251 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (1 / 800 : ℝ))) h 2
    have he :
        (Real.exp (1 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (1 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1 / 1 : ℝ) - (1 / 800 : ℝ) / 2) / 32)
      (110307911 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_1 :
    ∀ u : ℝ, (1 / 800 : ℝ) ≤ u → u ≤ (1 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (182806423 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (1 / 800 : ℝ) (1 / 400 : ℝ) (1002503 / 1000000 : ℝ) (15703347969 / 15625000000 : ℝ)
    (27583213 / 25000000 : ℝ) (107494189 / 2500000000 : ℝ) (182806423 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (1 / 800 : ℝ)) (1002503 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (1 / 400 : ℝ) (125313 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (1 / 400 : ℝ))) h 2
    have he :
        (Real.exp (1 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (1 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1002503 / 1000000 : ℝ) - (1 / 400 : ℝ) / 2) / 32)
      (27583213 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_2 :
    ∀ u : ℝ, (1 / 400 : ℝ) ≤ u → u ≤ (3 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (182800823 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (1 / 400 : ℝ) (3 / 800 : ℝ) (251253 / 250000 : ℝ) (251882530641 / 250000000000 : ℝ)
    (13794733 / 12500000 : ℝ) (426869227 / 10000000000 : ℝ) (182800823 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (1 / 400 : ℝ)) (251253 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (3 / 800 : ℝ) (501879 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (3 / 800 : ℝ))) h 2
    have he :
        (Real.exp (3 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (3 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (251253 / 250000 : ℝ) - (3 / 800 : ℝ) / 2) / 32)
      (13794733 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_3 :
    ∀ u : ℝ, (3 / 800 : ℝ) ≤ u → u ≤ (1 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (182788477 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (3 / 800 : ℝ) (1 / 200 : ℝ) (125941 / 125000 : ℝ) (1010051130169 / 1000000000000 : ℝ)
    (27595739 / 25000000 : ℝ) (16951001 / 400000000 : ℝ) (182788477 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (3 / 800 : ℝ)) (125941 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (1 / 200 : ℝ) (1005013 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (1 / 200 : ℝ))) h 2
    have he :
        (Real.exp (1 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (1 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (125941 / 125000 : ℝ) - (1 / 200 : ℝ) / 2) / 32)
      (27595739 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_4 :
    ∀ u : ℝ, (1 / 200 : ℝ) ≤ u → u ≤ (1 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (182771361 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (1 / 200 : ℝ) (1 / 160 : ℝ) (20201 / 20000 : ℝ) (10125793129 / 10000000000 : ℝ)
    (2760203 / 2500000 : ℝ) (3286681 / 78125000 : ℝ) (182771361 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (1 / 200 : ℝ)) (20201 / 20000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (1 / 160 : ℝ) (100627 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (1 / 160 : ℝ))) h 2
    have he :
        (Real.exp (1 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (1 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (20201 / 20000 : ℝ) - (1 / 160 : ℝ) / 2) / 32)
      (2760203 / 2500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_5 :
    ∀ u : ℝ, (1 / 160 : ℝ) ≤ u → u ≤ (3 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (22843699 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (1 / 160 : ℝ) (3 / 400 : ℝ) (506289 / 500000 : ℝ) (1015114685841 / 1000000000000 : ℝ)
    (55216677 / 50000000 : ℝ) (208814959 / 5000000000 : ℝ) (22843699 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (1 / 160 : ℝ)) (506289 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (3 / 400 : ℝ) (1007529 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (3 / 400 : ℝ))) h 2
    have he :
        (Real.exp (3 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (3 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (506289 / 500000 : ℝ) - (3 / 400 : ℝ) / 2) / 32)
      (55216677 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_6 :
    ∀ u : ℝ, (3 / 400 : ℝ) ≤ u → u ≤ (7 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (18272103 / 10000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (3 / 400 : ℝ) (7 / 800 : ℝ) (1015113 / 1000000 : ℝ) (1017655246521 / 1000000000000 : ℝ)
    (11045867 / 10000000 : ℝ) (82915569 / 2000000000 : ℝ) (18272103 / 10000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (3 / 400 : ℝ)) (1015113 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (7 / 800 : ℝ) (1008789 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (7 / 800 : ℝ))) h 2
    have he :
        (Real.exp (7 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (7 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1015113 / 1000000 : ℝ) - (7 / 800 : ℝ) / 2) / 32)
      (11045867 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_7 :
    ∀ u : ℝ, (7 / 800 : ℝ) ≤ u → u ≤ (1 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (91343897 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (7 / 800 : ℝ) (1 / 100 : ℝ) (508827 / 500000 : ℝ) (1020203022601 / 1000000000000 : ℝ)
    (110484057 / 100000000 : ℝ) (205770153 / 5000000000 : ℝ) (91343897 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (7 / 800 : ℝ)) (508827 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (1 / 100 : ℝ) (1010051 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (1 / 100 : ℝ))) h 2
    have he :
        (Real.exp (1 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (1 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (508827 / 500000 : ℝ) - (1 / 100 : ℝ) / 2) / 32)
      (110484057 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_8 :
    ∀ u : ℝ, (1 / 100 : ℝ) ≤ u → u ≤ (9 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (45662137 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (1 / 100 : ℝ) (9 / 800 : ℝ) (1020201 / 1000000 : ℝ) (255689001649 / 250000000000 : ℝ)
    (22101903 / 20000000 : ℝ) (204258657 / 5000000000 : ℝ) (45662137 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (1 / 100 : ℝ)) (1020201 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (9 / 800 : ℝ) (505657 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (9 / 800 : ℝ))) h 2
    have he :
        (Real.exp (9 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (9 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1020201 / 1000000 : ℝ) - (9 / 800 : ℝ) / 2) / 32)
      (22101903 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_9 :
    ∀ u : ℝ, (9 / 800 : ℝ) ≤ u → u ≤ (1 / 80 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (182603977 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (9 / 800 : ℝ) (1 / 80 : ℝ) (204551 / 200000 : ℝ) (1025316231241 / 1000000000000 : ℝ)
    (55267527 / 50000000 : ℝ) (405507707 / 10000000000 : ℝ) (182603977 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (9 / 800 : ℝ)) (204551 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (1 / 80 : ℝ) (1012579 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (1 / 80 : ℝ))) h 2
    have he :
        (Real.exp (1 / 80 : ℝ)) ^ 2 =
          Real.exp (2 * (1 / 80 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (204551 / 200000 : ℝ) - (1 / 80 : ℝ) / 2) / 32)
      (55267527 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_10 :
    ∀ u : ℝ, (1 / 80 : ℝ) ≤ u → u ≤ (11 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (182553387 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (1 / 80 : ℝ) (11 / 800 : ℝ) (205063 / 200000 : ℝ) (41115267361 / 40000000000 : ℝ)
    (22112133 / 20000000 : ℝ) (100628143 / 2500000000 : ℝ) (182553387 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (1 / 80 : ℝ)) (205063 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (11 / 800 : ℝ) (202769 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (11 / 800 : ℝ))) h 2
    have he :
        (Real.exp (11 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (11 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (205063 / 200000 : ℝ) - (11 / 800 : ℝ) / 2) / 32)
      (22112133 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_11 :
    ∀ u : ℝ, (11 / 800 : ℝ) ≤ u → u ≤ (3 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (182499571 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (11 / 800 : ℝ) (3 / 200 : ℝ) (1027881 / 1000000 : ℝ) (257614108249 / 250000000000 : ℝ)
    (55293173 / 50000000 : ℝ) (49941519 / 1250000000 : ℝ) (182499571 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (11 / 800 : ℝ)) (1027881 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (3 / 200 : ℝ) (507557 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (3 / 200 : ℝ))) h 2
    have he :
        (Real.exp (3 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (3 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1027881 / 1000000 : ℝ) - (3 / 200 : ℝ) / 2) / 32)
      (55293173 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_12 :
    ∀ u : ℝ, (3 / 200 : ℝ) ≤ u → u ≤ (13 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (182437713 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (3 / 200 : ℝ) (13 / 800 : ℝ) (515227 / 500000 : ℝ) (1033034402689 / 1000000000000 : ℝ)
    (11061211 / 10000000 : ℝ) (396564963 / 10000000000 : ℝ) (182437713 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (3 / 200 : ℝ)) (515227 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (13 / 800 : ℝ) (1016383 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (13 / 800 : ℝ))) h 2
    have he :
        (Real.exp (13 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (13 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (515227 / 500000 : ℝ) - (13 / 800 : ℝ) / 2) / 32)
      (11061211 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_13 :
    ∀ u : ℝ, (13 / 800 : ℝ) ≤ u → u ≤ (7 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (182372657 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (13 / 800 : ℝ) (7 / 400 : ℝ) (1033033 / 1000000 : ℝ) (41424867961 / 40000000000 : ℝ)
    (13829743 / 12500000 : ℝ) (98403131 / 2500000000 : ℝ) (182372657 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (13 / 800 : ℝ)) (1033033 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (7 / 400 : ℝ) (203531 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (7 / 400 : ℝ))) h 2
    have he :
        (Real.exp (7 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (7 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1033033 / 1000000 : ℝ) - (7 / 400 : ℝ) / 2) / 32)
      (13829743 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_14 :
    ∀ u : ℝ, (7 / 400 : ℝ) ≤ u → u ≤ (3 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (182299619 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (7 / 400 : ℝ) (3 / 160 : ℝ) (1035619 / 1000000 : ℝ) (1038212231329 / 1000000000000 : ℝ)
    (110663861 / 100000000 : ℝ) (97668343 / 2500000000 : ℝ) (182299619 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (7 / 400 : ℝ)) (1035619 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (3 / 160 : ℝ) (1018927 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (3 / 160 : ℝ))) h 2
    have he :
        (Real.exp (3 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (3 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1035619 / 1000000 : ℝ) - (3 / 160 : ℝ) / 2) / 32)
      (110663861 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_15 :
    ∀ u : ℝ, (3 / 160 : ℝ) ≤ u → u ≤ (1 / 50 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (45555839 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (3 / 160 : ℝ) (1 / 50 : ℝ) (1038211 / 1000000 : ℝ) (260203030201 / 250000000000 : ℝ)
    (110689849 / 100000000 : ℝ) (48468611 / 1250000000 : ℝ) (45555839 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (3 / 160 : ℝ)) (1038211 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (1 / 50 : ℝ) (510101 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (1 / 50 : ℝ))) h 2
    have he :
        (Real.exp (1 / 50 : ℝ)) ^ 2 =
          Real.exp (2 * (1 / 50 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1038211 / 1000000 : ℝ) - (1 / 50 : ℝ) / 2) / 32)
      (110689849 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_16 :
    ∀ u : ℝ, (1 / 50 : ℝ) ≤ u → u ≤ (17 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (45535133 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (1 / 50 : ℝ) (17 / 800 : ℝ) (104081 / 100000 : ℝ) (260854326121 / 250000000000 : ℝ)
    (110715919 / 100000000 : ℝ) (192418927 / 5000000000 : ℝ) (45535133 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (1 / 50 : ℝ)) (104081 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (17 / 800 : ℝ) (510739 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (17 / 800 : ℝ))) h 2
    have he :
        (Real.exp (17 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (17 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (104081 / 100000 : ℝ) - (17 / 800 : ℝ) / 2) / 32)
      (110715919 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_17 :
    ∀ u : ℝ, (17 / 800 : ℝ) ≤ u → u ≤ (9 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (91026239 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (17 / 800 : ℝ) (9 / 400 : ℝ) (130427 / 125000 : ℝ) (65376864721 / 62500000000 : ℝ)
    (110742071 / 100000000 : ℝ) (190970151 / 5000000000 : ℝ) (91026239 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (17 / 800 : ℝ)) (130427 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (9 / 400 : ℝ) (255689 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (9 / 400 : ℝ))) h 2
    have he :
        (Real.exp (9 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (9 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (130427 / 125000 : ℝ) - (9 / 400 : ℝ) / 2) / 32)
      (110742071 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_18 :
    ∀ u : ℝ, (9 / 400 : ℝ) ≤ u → u ≤ (19 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (45489827 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (9 / 400 : ℝ) (19 / 800 : ℝ) (1046027 / 1000000 : ℝ) (41945907249 / 40000000000 : ℝ)
    (27692071 / 25000000 : ℝ) (379058563 / 10000000000 : ℝ) (45489827 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (9 / 400 : ℝ)) (1046027 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (19 / 800 : ℝ) (204807 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (19 / 800 : ℝ))) h 2
    have he :
        (Real.exp (19 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (19 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1046027 / 1000000 : ℝ) - (19 / 800 : ℝ) / 2) / 32)
      (27692071 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_19 :
    ∀ u : ℝ, (19 / 800 : ℝ) ≤ u → u ≤ (1 / 40 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (18186023 / 10000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (19 / 800 : ℝ) (1 / 40 : ℝ) (524323 / 500000 : ℝ) (65704556241 / 62500000000 : ℝ)
    (11079459 / 10000000 : ℝ) (376189137 / 10000000000 : ℝ) (18186023 / 10000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (19 / 800 : ℝ)) (524323 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (1 / 40 : ℝ) (256329 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (1 / 40 : ℝ))) h 2
    have he :
        (Real.exp (1 / 40 : ℝ)) ^ 2 =
          Real.exp (2 * (1 / 40 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (524323 / 500000 : ℝ) - (1 / 40 : ℝ) / 2) / 32)
      (11079459 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_0
#print axioms hpThetaEnergyUpper_interval_19

end HodgeProofHP
