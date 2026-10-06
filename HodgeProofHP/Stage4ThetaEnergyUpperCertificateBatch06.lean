import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_120 :
    ∀ u : ℝ, (3 / 20 : ℝ) ≤ u → u ≤ (121 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (29490223 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (3 / 20 : ℝ) (121 / 800 : ℝ) (674929 / 500000 : ℝ) (21144358921 / 15625000000 : ℝ)
    (113893263 / 100000000 : ℝ) (9726193 / 625000000 : ℝ) (29490223 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (3 / 20 : ℝ)) (674929 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (121 / 800 : ℝ) (145411 / 125000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (121 / 800 : ℝ))) h 2
    have he :
        (Real.exp (121 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (121 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (674929 / 500000 : ℝ) - (121 / 800 : ℝ) / 2) / 32)
      (113893263 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_121 :
    ∀ u : ℝ, (121 / 800 : ℝ) ≤ u → u ≤ (61 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (73457519 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (121 / 800 : ℝ) (61 / 400 : ℝ) (1353237 / 1000000 : ℝ) (1356626256049 / 1000000000000 : ℝ)
    (113928807 / 100000000 : ℝ) (30814591 / 2000000000 : ℝ) (73457519 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (121 / 800 : ℝ)) (1353237 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (61 / 400 : ℝ) (1164743 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (61 / 400 : ℝ))) h 2
    have he :
        (Real.exp (61 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (61 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1353237 / 1000000 : ℝ) - (61 / 400 : ℝ) / 2) / 32)
      (113928807 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_122 :
    ∀ u : ℝ, (61 / 400 : ℝ) ≤ u → u ≤ (123 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (36594039 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (61 / 400 : ℝ) (123 / 800 : ℝ) (10853 / 8000 : ℝ) (34000561 / 25000000 : ℝ)
    (56982231 / 50000000 : ℝ) (152537903 / 10000000000 : ℝ) (36594039 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (61 / 400 : ℝ)) (10853 / 8000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (123 / 800 : ℝ) (5831 / 5000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (123 / 800 : ℝ))) h 2
    have he :
        (Real.exp (123 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (123 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (10853 / 8000 : ℝ) - (123 / 800 : ℝ) / 2) / 32)
      (56982231 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_123 :
    ∀ u : ℝ, (123 / 800 : ℝ) ≤ u → u ≤ (31 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (36458673 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (123 / 800 : ℝ) (31 / 200 : ℝ) (68001 / 50000 : ℝ) (340856301241 / 250000000000 : ℝ)
    (7125013 / 6250000 : ℝ) (75507381 / 5000000000 : ℝ) (36458673 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (123 / 800 : ℝ)) (68001 / 50000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (31 / 200 : ℝ) (583829 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (31 / 200 : ℝ))) h 2
    have he :
        (Real.exp (31 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (31 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (68001 / 50000 : ℝ) - (31 / 200 : ℝ) / 2) / 32)
      (7125013 / 6250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_124 :
    ∀ u : ℝ, (31 / 200 : ℝ) ≤ u → u ≤ (5 / 32 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (29058157 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (31 / 200 : ℝ) (5 / 32 : ℝ) (54537 / 40000 : ℝ) (1366839236161 / 1000000000000 : ℝ)
    (28509019 / 25000000 : ℝ) (149502181 / 10000000000 : ℝ) (29058157 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (31 / 200 : ℝ)) (54537 / 40000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (5 / 32 : ℝ) (1169119 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (5 / 32 : ℝ))) h 2
    have he :
        (Real.exp (5 / 32 : ℝ)) ^ 2 =
          Real.exp (2 * (5 / 32 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (54537 / 40000 : ℝ) - (5 / 32 : ℝ) / 2) / 32)
      (28509019 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_125 :
    ∀ u : ℝ, (5 / 32 : ℝ) ≤ u → u ≤ (63 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (28948887 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (5 / 32 : ℝ) (63 / 400 : ℝ) (1366837 / 1000000 : ℝ) (1370259877561 / 1000000000000 : ℝ)
    (57036017 / 50000000 : ℝ) (148001483 / 10000000000 : ℝ) (28948887 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (5 / 32 : ℝ)) (1366837 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (63 / 400 : ℝ) (1170581 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (63 / 400 : ℝ))) h 2
    have he :
        (Real.exp (63 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (63 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1366837 / 1000000 : ℝ) - (63 / 400 : ℝ) / 2) / 32)
      (57036017 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_126 :
    ∀ u : ℝ, (63 / 400 : ℝ) ≤ u → u ≤ (127 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (72097473 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (63 / 400 : ℝ) (127 / 800 : ℝ) (1370259 / 1000000 : ℝ) (54947579281 / 40000000000 : ℝ)
    (22821623 / 20000000 : ℝ) (146511261 / 10000000000 : ℝ) (72097473 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (63 / 400 : ℝ)) (1370259 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (127 / 800 : ℝ) (234409 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (127 / 800 : ℝ))) h 2
    have he :
        (Real.exp (127 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (127 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1370259 / 1000000 : ℝ) - (127 / 800 : ℝ) / 2) / 32)
      (22821623 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_127 :
    ∀ u : ℝ, (127 / 800 : ℝ) ≤ u → u ≤ (4 / 25 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (35910843 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (127 / 800 : ℝ) (4 / 25 : ℝ) (1373689 / 1000000 : ℝ) (1377128067121 / 1000000000000 : ℝ)
    (114144297 / 100000000 : ℝ) (145032401 / 10000000000 : ℝ) (35910843 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (127 / 800 : ℝ)) (1373689 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (4 / 25 : ℝ) (1173511 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (4 / 25 : ℝ))) h 2
    have he :
        (Real.exp (4 / 25 : ℝ)) ^ 2 =
          Real.exp (2 * (4 / 25 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1373689 / 1000000 : ℝ) - (4 / 25 : ℝ) / 2) / 32)
      (114144297 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_128 :
    ∀ u : ℝ, (4 / 25 : ℝ) ≤ u → u ≤ (129 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (71544859 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (4 / 25 : ℝ) (129 / 800 : ℝ) (1377127 / 1000000 : ℝ) (1380575650441 / 1000000000000 : ℝ)
    (114180581 / 100000000 : ℝ) (71782413 / 5000000000 : ℝ) (71544859 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (4 / 25 : ℝ)) (1377127 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (129 / 800 : ℝ) (1174979 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (129 / 800 : ℝ))) h 2
    have he :
        (Real.exp (129 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (129 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1377127 / 1000000 : ℝ) - (129 / 800 : ℝ) / 2) / 32)
      (114180581 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_129 :
    ∀ u : ℝ, (129 / 800 : ℝ) ≤ u → u ≤ (13 / 80 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (142533577 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (129 / 800 : ℝ) (13 / 80 : ℝ) (690287 / 500000 : ℝ) (1384032249601 / 1000000000000 : ℝ)
    (114216977 / 100000000 : ℝ) (142108101 / 10000000000 : ℝ) (142533577 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (129 / 800 : ℝ)) (690287 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (13 / 80 : ℝ) (1176449 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (13 / 80 : ℝ))) h 2
    have he :
        (Real.exp (13 / 80 : ℝ)) ^ 2 =
          Real.exp (2 * (13 / 80 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (690287 / 500000 : ℝ) - (13 / 80 : ℝ) / 2) / 32)
      (114216977 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_130 :
    ∀ u : ℝ, (13 / 80 : ℝ) ≤ u → u ≤ (131 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (141974269 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (13 / 80 : ℝ) (131 / 800 : ℝ) (138403 / 100000 : ℝ) (13549761 / 9765625 : ℝ)
    (22850697 / 20000000 : ℝ) (70331101 / 5000000000 : ℝ) (141974269 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (13 / 80 : ℝ)) (138403 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (131 / 800 : ℝ) (3681 / 3125 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (131 / 800 : ℝ))) h 2
    have he :
        (Real.exp (131 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (131 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (138403 / 100000 : ℝ) - (131 / 800 : ℝ) / 2) / 32)
      (22850697 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_131 :
    ∀ u : ℝ, (131 / 800 : ℝ) ≤ u → u ≤ (33 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (5656531 / 4000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (131 / 800 : ℝ) (33 / 200 : ℝ) (277499 / 200000 : ℝ) (347742551809 / 250000000000 : ℝ)
    (57145053 / 50000000 : ℝ) (17403383 / 1250000000 : ℝ) (5656531 / 4000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (131 / 800 : ℝ)) (277499 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (33 / 200 : ℝ) (589697 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (33 / 200 : ℝ))) h 2
    have he :
        (Real.exp (33 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (33 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (277499 / 200000 : ℝ) - (33 / 200 : ℝ) / 2) / 32)
      (57145053 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_132 :
    ∀ u : ℝ, (33 / 200 : ℝ) ≤ u → u ≤ (133 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (28169943 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (33 / 200 : ℝ) (133 / 800 : ℝ) (173871 / 125000 : ℝ) (1394451595161 / 1000000000000 : ℝ)
    (28581707 / 25000000 : ℝ) (68901563 / 5000000000 : ℝ) (28169943 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (33 / 200 : ℝ)) (173871 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (133 / 800 : ℝ) (1180869 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (133 / 800 : ℝ))) h 2
    have he :
        (Real.exp (133 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (133 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (173871 / 125000 : ℝ) - (133 / 800 : ℝ) / 2) / 32)
      (28581707 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_133 :
    ∀ u : ℝ, (133 / 800 : ℝ) ≤ u → u ≤ (67 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (35071081 / 25000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (133 / 800 : ℝ) (67 / 400 : ℝ) (1394449 / 1000000 : ℝ) (349485515929 / 250000000000 : ℝ)
    (28590913 / 25000000 : ℝ) (34097577 / 2500000000 : ℝ) (35071081 / 25000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (133 / 800 : ℝ)) (1394449 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (67 / 400 : ℝ) (591173 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (67 / 400 : ℝ))) h 2
    have he :
        (Real.exp (67 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (67 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1394449 / 1000000 : ℝ) - (67 / 400 : ℝ) / 2) / 32)
      (28590913 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_134 :
    ∀ u : ℝ, (67 / 400 : ℝ) ≤ u → u ≤ (27 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (139716187 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (67 / 400 : ℝ) (27 / 160 : ℝ) (69897 / 50000 : ℝ) (2242306609 / 1600000000 : ℝ)
    (572003 / 500000 : ℝ) (134987741 / 10000000000 : ℝ) (139716187 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (67 / 400 : ℝ)) (69897 / 50000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (27 / 160 : ℝ) (47353 / 40000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (27 / 160 : ℝ))) h 2
    have he :
        (Real.exp (27 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (27 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (69897 / 50000 : ℝ) - (27 / 160 : ℝ) / 2) / 32)
      (572003 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_135 :
    ∀ u : ℝ, (27 / 160 : ℝ) ≤ u → u ≤ (17 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (139145611 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (27 / 160 : ℝ) (17 / 100 : ℝ) (1401439 / 1000000 : ℝ) (56197917721 / 40000000000 : ℝ)
    (2288753 / 2000000 : ℝ) (133596233 / 10000000000 : ℝ) (139145611 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (27 / 160 : ℝ)) (1401439 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (17 / 100 : ℝ) (237061 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (17 / 100 : ℝ))) h 2
    have he :
        (Real.exp (17 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (17 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1401439 / 1000000 : ℝ) - (17 / 100 : ℝ) / 2) / 32)
      (2288753 / 2000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_136 :
    ∀ u : ℝ, (17 / 100 : ℝ) ≤ u → u ≤ (137 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (138573587 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (17 / 100 : ℝ) (137 / 800 : ℝ) (1404947 / 1000000 : ℝ) (88029109809 / 62500000000 : ℝ)
    (114474813 / 100000000 : ℝ) (16526917 / 1250000000 : ℝ) (138573587 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (17 / 100 : ℝ)) (1404947 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (137 / 800 : ℝ) (296697 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (137 / 800 : ℝ))) h 2
    have he :
        (Real.exp (137 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (137 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1404947 / 1000000 : ℝ) - (137 / 800 : ℝ) / 2) / 32)
      (114474813 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_137 :
    ∀ u : ℝ, (137 / 800 : ℝ) ≤ u → u ≤ (69 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (27599751 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (137 / 800 : ℝ) (69 / 400 : ℝ) (88029 / 62500 : ℝ) (5515587289 / 3906250000 : ℝ)
    (114512089 / 100000000 : ℝ) (65422511 / 5000000000 : ℝ) (27599751 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (137 / 800 : ℝ)) (88029 / 62500 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (69 / 400 : ℝ) (74267 / 62500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (69 / 400 : ℝ))) h 2
    have he :
        (Real.exp (69 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (69 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (88029 / 62500 : ℝ) - (69 / 400 : ℝ) / 2) / 32)
      (114512089 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_138 :
    ∀ u : ℝ, (69 / 400 : ℝ) ≤ u → u ≤ (139 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (137423041 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (69 / 400 : ℝ) (139 / 800 : ℝ) (1411989 / 1000000 : ℝ) (1415526478081 / 1000000000000 : ℝ)
    (114549467 / 100000000 : ℝ) (6474283 / 500000000 : ℝ) (137423041 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (69 / 400 : ℝ)) (1411989 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (139 / 800 : ℝ) (1189759 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (139 / 800 : ℝ))) h 2
    have he :
        (Real.exp (139 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (139 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1411989 / 1000000 : ℝ) - (139 / 800 : ℝ) / 2) / 32)
      (114549467 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_139 :
    ∀ u : ℝ, (139 / 800 : ℝ) ≤ u → u ≤ (7 / 40 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (68422059 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (139 / 800 : ℝ) (7 / 40 : ℝ) (353881 / 250000 : ℝ) (1419069415009 / 1000000000000 : ℝ)
    (11458697 / 10000000 : ℝ) (128136383 / 10000000000 : ℝ) (68422059 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (139 / 800 : ℝ)) (353881 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (7 / 40 : ℝ) (1191247 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (7 / 40 : ℝ))) h 2
    have he :
        (Real.exp (7 / 40 : ℝ)) ^ 2 =
          Real.exp (2 * (7 / 40 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (353881 / 250000 : ℝ) - (7 / 40 : ℝ) / 2) / 32)
      (11458697 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_120
#print axioms hpThetaEnergyUpper_interval_139

end HodgeProofHP
