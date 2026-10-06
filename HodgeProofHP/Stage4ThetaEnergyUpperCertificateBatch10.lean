import HodgeProofHP.Stage4ThetaKernelIntervalUpper

/-! Explicit rational upper certificates on twenty intervals. -/

noncomputable section

namespace HodgeProofHP

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_200 :
    ∀ u : ℝ, (1 / 4 : ℝ) ≤ u → u ≤ (201 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (99301223 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (1 / 4 : ℝ) (201 / 800 : ℝ) (1648721 / 1000000 : ℝ) (403527744 / 244140625 : ℝ)
    (58549817 / 50000000 : ℝ) (64006311 / 10000000000 : ℝ) (99301223 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (1 / 4 : ℝ)) (1648721 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (201 / 800 : ℝ) (20088 / 15625 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (201 / 800 : ℝ))) h 2
    have he :
        (Real.exp (201 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (201 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1648721 / 1000000 : ℝ) - (201 / 800 : ℝ) / 2) / 32)
      (58549817 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_201 :
    ∀ u : ℝ, (201 / 800 : ℝ) ≤ u → u ≤ (101 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (49337209 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (201 / 800 : ℝ) (101 / 400 : ℝ) (103303 / 62500 : ℝ) (1035616761 / 625000000 : ℝ)
    (117144777 / 100000000 : ℝ) (63221711 / 10000000000 : ℝ) (49337209 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (201 / 800 : ℝ)) (103303 / 62500 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (101 / 400 : ℝ) (32181 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (101 / 400 : ℝ))) h 2
    have he :
        (Real.exp (101 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (101 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (103303 / 62500 : ℝ) - (101 / 400 : ℝ) / 2) / 32)
      (117144777 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_202 :
    ∀ u : ℝ, (101 / 400 : ℝ) ≤ u → u ≤ (203 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (98048159 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (101 / 400 : ℝ) (203 / 800 : ℝ) (331397 / 200000 : ℝ) (664453729 / 400000000 : ℝ)
    (29297513 / 25000000 : ℝ) (31222387 / 5000000000 : ℝ) (98048159 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (101 / 400 : ℝ)) (331397 / 200000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (203 / 800 : ℝ) (25777 / 20000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (203 / 800 : ℝ))) h 2
    have he :
        (Real.exp (203 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (203 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (331397 / 200000 : ℝ) - (203 / 800 : ℝ) / 2) / 32)
      (29297513 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_203 :
    ∀ u : ℝ, (203 / 800 : ℝ) ≤ u → u ≤ (51 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (97422153 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (203 / 800 : ℝ) (51 / 200 : ℝ) (1661133 / 1000000 : ℝ) (416323043361 / 250000000000 : ℝ)
    (117235471 / 100000000 : ℝ) (7709407 / 1250000000 : ℝ) (97422153 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (203 / 800 : ℝ)) (1661133 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (51 / 200 : ℝ) (645231 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (51 / 200 : ℝ))) h 2
    have he :
        (Real.exp (51 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (51 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1661133 / 1000000 : ℝ) - (51 / 200 : ℝ) / 2) / 32)
      (117235471 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_204 :
    ∀ u : ℝ, (51 / 200 : ℝ) ≤ u → u ≤ (41 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (96796787 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (51 / 200 : ℝ) (41 / 160 : ℝ) (1665291 / 1000000 : ℝ) (104341274361 / 62500000000 : ℝ)
    (58640511 / 50000000 : ℝ) (60913319 / 10000000000 : ℝ) (96796787 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (51 / 200 : ℝ)) (1665291 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (41 / 160 : ℝ) (323019 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (41 / 160 : ℝ))) h 2
    have he :
        (Real.exp (41 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (41 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1665291 / 1000000 : ℝ) - (41 / 160 : ℝ) / 2) / 32)
      (58640511 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_205 :
    ∀ u : ℝ, (41 / 160 : ℝ) ≤ u → u ≤ (103 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (19234411 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (41 / 160 : ℝ) (103 / 400 : ℝ) (1669459 / 1000000 : ℝ) (104602436929 / 62500000000 : ℝ)
    (117326707 / 100000000 : ℝ) (60158887 / 10000000000 : ℝ) (19234411 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (41 / 160 : ℝ)) (1669459 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (103 / 400 : ℝ) (323423 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (103 / 400 : ℝ))) h 2
    have he :
        (Real.exp (103 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (103 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1669459 / 1000000 : ℝ) - (103 / 400 : ℝ) / 2) / 32)
      (117326707 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_206 :
    ∀ u : ℝ, (103 / 400 : ℝ) ≤ u → u ≤ (207 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (95547717 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (103 / 400 : ℝ) (207 / 800 : ℝ) (836819 / 500000 : ℝ) (16778279961 / 10000000000 : ℝ)
    (14671567 / 12500000 : ℝ) (11882351 / 2000000000 : ℝ) (95547717 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (103 / 400 : ℝ)) (836819 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (207 / 800 : ℝ) (129531 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (207 / 800 : ℝ))) h 2
    have he :
        (Real.exp (207 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (207 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (836819 / 500000 : ℝ) - (207 / 800 : ℝ) / 2) / 32)
      (14671567 / 12500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_207 :
    ∀ u : ℝ, (207 / 800 : ℝ) ≤ u → u ≤ (13 / 50 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (47462269 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (207 / 800 : ℝ) (13 / 50 : ℝ) (1677827 / 1000000 : ℝ) (1682030018761 / 1000000000000 : ℝ)
    (58709249 / 50000000 : ℝ) (58672061 / 10000000000 : ℝ) (47462269 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (207 / 800 : ℝ)) (1677827 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (13 / 50 : ℝ) (1296931 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (13 / 50 : ℝ))) h 2
    have he :
        (Real.exp (13 / 50 : ℝ)) ^ 2 =
          Real.exp (2 * (13 / 50 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1677827 / 1000000 : ℝ) - (13 / 50 : ℝ) / 2) / 32)
      (58709249 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_208 :
    ∀ u : ℝ, (13 / 50 : ℝ) ≤ u → u ≤ (209 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (94301437 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (13 / 50 : ℝ) (209 / 800 : ℝ) (1682027 / 1000000 : ℝ) (1686239893809 / 1000000000000 : ℝ)
    (29366151 / 25000000 : ℝ) (57939587 / 10000000000 : ℝ) (94301437 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (13 / 50 : ℝ)) (1682027 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (209 / 800 : ℝ) (1298553 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (209 / 800 : ℝ))) h 2
    have he :
        (Real.exp (209 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (209 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1682027 / 1000000 : ℝ) - (209 / 800 : ℝ) / 2) / 32)
      (29366151 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_209 :
    ∀ u : ℝ, (209 / 800 : ℝ) ≤ u → u ≤ (21 / 80 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (93679127 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (209 / 800 : ℝ) (21 / 80 : ℝ) (1686237 / 1000000 : ℝ) (1690460231329 / 1000000000000 : ℝ)
    (23502169 / 20000000 : ℝ) (57214437 / 10000000000 : ℝ) (93679127 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (209 / 800 : ℝ)) (1686237 / 1000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (21 / 80 : ℝ) (1300177 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (21 / 80 : ℝ))) h 2
    have he :
        (Real.exp (21 / 80 : ℝ)) ^ 2 =
          Real.exp (2 * (21 / 80 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (1686237 / 1000000 : ℝ) - (21 / 80 : ℝ) / 2) / 32)
      (23502169 / 20000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_210 :
    ∀ u : ℝ, (21 / 80 : ℝ) ≤ u → u ≤ (211 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (465287 / 500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (21 / 80 : ℝ) (211 / 800 : ℝ) (845229 / 500000 : ℝ) (1694691050809 / 1000000000000 : ℝ)
    (11755723 / 10000000 : ℝ) (14124107 / 2500000000 : ℝ) (465287 / 500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (21 / 80 : ℝ)) (845229 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (211 / 800 : ℝ) (1301803 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (211 / 800 : ℝ))) h 2
    have he :
        (Real.exp (211 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (211 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (845229 / 500000 : ℝ) - (211 / 800 : ℝ) / 2) / 32)
      (11755723 / 10000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_211 :
    ∀ u : ℝ, (211 / 800 : ℝ) ≤ u → u ≤ (53 / 200 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (18487251 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (211 / 800 : ℝ) (53 / 200 : ℝ) (169469 / 100000 : ℝ) (1698932371761 / 1000000000000 : ℝ)
    (117603761 / 100000000 : ℝ) (55785491 / 10000000000 : ℝ) (18487251 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (211 / 800 : ℝ)) (169469 / 100000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (53 / 200 : ℝ) (1303431 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (53 / 200 : ℝ))) h 2
    have he :
        (Real.exp (53 / 200 : ℝ)) ^ 2 =
          Real.exp (2 * (53 / 200 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (169469 / 100000 : ℝ) - (53 / 200 : ℝ) / 2) / 32)
      (117603761 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_212 :
    ∀ u : ℝ, (53 / 200 : ℝ) ≤ u → u ≤ (213 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (45908237 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (53 / 200 : ℝ) (213 / 800 : ℝ) (424733 / 250000 : ℝ) (425796705961 / 250000000000 : ℝ)
    (4706017 / 4000000 : ℝ) (55081783 / 10000000000 : ℝ) (45908237 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (53 / 200 : ℝ)) (424733 / 250000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (213 / 800 : ℝ) (652531 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (213 / 800 : ℝ))) h 2
    have he :
        (Real.exp (213 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (213 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (424733 / 250000 : ℝ) - (213 / 800 : ℝ) / 2) / 32)
      (4706017 / 4000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_213 :
    ∀ u : ℝ, (213 / 800 : ℝ) ≤ u → u ≤ (107 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (91197293 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (213 / 800 : ℝ) (107 / 400 : ℝ) (106449 / 62500 : ℝ) (426862302409 / 250000000000 : ℝ)
    (117697223 / 100000000 : ℝ) (10877049 / 2000000000 : ℝ) (91197293 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (213 / 800 : ℝ)) (106449 / 62500 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (107 / 400 : ℝ) (653347 / 500000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (107 / 400 : ℝ))) h 2
    have he :
        (Real.exp (107 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (107 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (106449 / 62500 : ℝ) - (107 / 400 : ℝ) / 2) / 32)
      (117697223 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_214 :
    ∀ u : ℝ, (107 / 400 : ℝ) ≤ u → u ≤ (43 / 160 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (18115779 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (107 / 400 : ℝ) (43 / 160 : ℝ) (213431 / 125000 : ℝ) (1711724772241 / 1000000000000 : ℝ)
    (117744179 / 100000000 : ℝ) (53695481 / 10000000000 : ℝ) (18115779 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (107 / 400 : ℝ)) (213431 / 125000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (43 / 160 : ℝ) (1308329 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (43 / 160 : ℝ))) h 2
    have he :
        (Real.exp (43 / 160 : ℝ)) ^ 2 =
          Real.exp (2 * (43 / 160 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (213431 / 125000 : ℝ) - (43 / 160 : ℝ) / 2) / 32)
      (117744179 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_215 :
    ∀ u : ℝ, (43 / 160 : ℝ) ≤ u → u ≤ (27 / 100 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (11245149 / 12500000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (43 / 160 : ℝ) (27 / 100 : ℝ) (855861 / 500000 : ℝ) (68640332049 / 40000000000 : ℝ)
    (117791269 / 100000000 : ℝ) (10602561 / 2000000000 : ℝ) (11245149 / 12500000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (43 / 160 : ℝ)) (855861 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (27 / 100 : ℝ) (261993 / 200000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (27 / 100 : ℝ))) h 2
    have he :
        (Real.exp (27 / 100 : ℝ)) ^ 2 =
          Real.exp (2 * (27 / 100 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (855861 / 500000 : ℝ) - (27 / 100 : ℝ) / 2) / 32)
      (117791269 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_216 :
    ∀ u : ℝ, (27 / 100 : ℝ) ≤ u → u ≤ (217 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (89344587 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (27 / 100 : ℝ) (217 / 800 : ℝ) (858003 / 500000 : ℝ) (1720302429609 / 1000000000000 : ℝ)
    (58919247 / 50000000 : ℝ) (26168579 / 5000000000 : ℝ) (89344587 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (27 / 100 : ℝ)) (858003 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (217 / 800 : ℝ) (1311603 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (217 / 800 : ℝ))) h 2
    have he :
        (Real.exp (217 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (217 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (858003 / 500000 : ℝ) - (217 / 800 : ℝ) / 2) / 32)
      (58919247 / 50000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_217 :
    ∀ u : ℝ, (217 / 800 : ℝ) ≤ u → u ≤ (109 / 400 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (44364461 / 50000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (217 / 800 : ℝ) (109 / 400 : ℝ) (860151 / 500000 : ℝ) (107788112721 / 62500000000 : ℝ)
    (29471469 / 25000000 : ℝ) (10333637 / 2000000000 : ℝ) (44364461 / 50000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (217 / 800 : ℝ)) (860151 / 500000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (109 / 400 : ℝ) (328311 / 250000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (109 / 400 : ℝ))) h 2
    have he :
        (Real.exp (109 / 400 : ℝ)) ^ 2 =
          Real.exp (2 * (109 / 400 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (860151 / 500000 : ℝ) - (109 / 400 : ℝ) / 2) / 32)
      (29471469 / 25000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_218 :
    ∀ u : ℝ, (109 / 400 : ℝ) ≤ u → u ≤ (219 / 800 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (88114433 / 100000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (109 / 400 : ℝ) (219 / 800 : ℝ) (26947 / 15625 : ℝ) (1728927822769 / 1000000000000 : ℝ)
    (117933393 / 100000000 : ℝ) (25503079 / 5000000000 : ℝ) (88114433 / 100000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (109 / 400 : ℝ)) (26947 / 15625 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (219 / 800 : ℝ) (1314887 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (219 / 800 : ℝ))) h 2
    have he :
        (Real.exp (219 / 800 : ℝ)) ^ 2 =
          Real.exp (2 * (219 / 800 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (26947 / 15625 : ℝ) - (219 / 800 : ℝ) / 2) / 32)
      (117933393 / 100000000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

-- Taylor arithmetic and the thirty-second power use large rationals.
set_option maxHeartbeats 2000000 in
theorem hpThetaEnergyUpper_interval_219 :
    ∀ u : ℝ, (219 / 800 : ℝ) ≤ u → u ≤ (11 / 40 : ℝ) →
      hpRiemannThetaDifferentialKernel u ≤ (17500103 / 20000000 : ℝ) := by
  apply hpThetaKernel_rational_interval_upper_certificate
    (219 / 800 : ℝ) (11 / 40 : ℝ) (69157 / 40000 : ℝ) (1733253873961 / 1000000000000 : ℝ)
    (921727 / 781250 : ℝ) (50350881 / 10000000000 : ℝ) (17500103 / 20000000 : ℝ)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (219 / 800 : ℝ)) (69157 / 40000 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaTrace_exp_upper_of_taylor
      (11 / 40 : ℝ) (1316531 / 1000000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    have hs := pow_le_pow_left₀
      (le_of_lt (Real.exp_pos (11 / 40 : ℝ))) h 2
    have he :
        (Real.exp (11 / 40 : ℝ)) ^ 2 =
          Real.exp (2 * (11 / 40 : ℝ)) := by
      rw [hpThetaKernelUpper_exp_pow]
      congr 1
      ring
    rw [he] at hs
    norm_num at hs ⊢
    exact hs
  · exact hpThetaTrace_exp_lower_of_taylor
      (((157 / 50 : ℝ) * (69157 / 40000 : ℝ) - (11 / 40 : ℝ) / 2) / 32)
      (921727 / 781250 : ℝ) 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num

#print axioms hpThetaEnergyUpper_interval_200
#print axioms hpThetaEnergyUpper_interval_219

end HodgeProofHP
