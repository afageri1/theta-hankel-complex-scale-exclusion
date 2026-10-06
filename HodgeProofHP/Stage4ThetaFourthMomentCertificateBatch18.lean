import HodgeProofHP.Stage4ThetaFourthMomentCertificateBase

/-! A finite batch of kernel-checked fourth-moment interval certificates. -/

-- Each batch contains twenty explicit exponential certificates.
set_option maxHeartbeats 0
set_option maxRecDepth 10000

noncomputable section

namespace HodgeProofHP

theorem hpThetaFourthCertificate_endpoint_360 :
    (19 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (9 / 10 : ℝ) (361 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (9 / 10 : ℝ) (361 / 400 : ℝ) (1512411 / 250000 : ℝ) (237498921 / 39062500 : ℝ)
    (3218353476529 / 1000000000000 : ℝ) (3 / 400000000 : ℝ) (19 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (9 / 10 : ℝ)) (1512411 / 250000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (361 / 400 : ℝ)) (15411 / 6250 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (14610869523 / 12500000000 : ℝ) (1793977 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_361 :
    (9 / 500000 : ℝ) ≤ hpThetaTraceEndpointLower (361 / 400 : ℝ) (181 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (361 / 400 : ℝ) (181 / 200 : ℝ) (189999 / 31250 : ℝ) (381902988289 / 62500000000 : ℝ)
    (3237469694209 / 1000000000000 : ℝ) (17 / 2500000000 : ℝ) (9 / 500000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (361 / 400 : ℝ)) (189999 / 31250 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (181 / 200 : ℝ)) (617983 / 250000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (23495825762207 / 20000000000000 : ℝ) (1799297 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_362 :
    (1 / 62500 : ℝ) ≤ hpThetaTraceEndpointLower (181 / 200 : ℝ) (363 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (181 / 200 : ℝ) (363 / 400 : ℝ) (1527611 / 250000 : ℝ) (3838174209 / 625000000 : ℝ)
    (8141994289 / 2500000000 : ℝ) (31 / 5000000000 : ℝ) (1 / 62500 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (181 / 200 : ℝ)) (1527611 / 250000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (363 / 400 : ℝ)) (61953 / 25000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (236148725167 / 200000000000 : ℝ) (90233 / 50000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_363 :
    (3 / 200000 : ℝ) ≤ hpThetaTraceEndpointLower (363 / 400 : ℝ) (91 / 100 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (363 / 400 : ℝ) (91 / 100 : ℝ) (6141073 / 1000000 : ℝ) (6171860768329 / 1000000000000 : ℝ)
    (819084731089 / 250000000000 : ℝ) (7 / 1250000000 : ℝ) (3 / 200000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (363 / 400 : ℝ)) (6141073 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (91 / 100 : ℝ)) (2484323 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (379752228404727 / 320000000000000 : ℝ) (905033 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_364 :
    (7 / 500000 : ℝ) ≤ hpThetaTraceEndpointLower (91 / 100 : ℝ) (73 / 80 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (91 / 100 : ℝ) (73 / 80 : ℝ) (1234371 / 200000 : ℝ) (1550699863441 / 250000000000 : ℝ)
    (206006146641 / 62500000000 : ℝ) (51 / 10000000000 : ℝ) (7 / 500000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (91 / 100 : ℝ)) (1234371 / 200000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (73 / 80 : ℝ)) (1245271 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (95419091396783 / 80000000000000 : ℝ) (453879 / 250000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_365 :
    (3 / 250000 : ℝ) ≤ hpThetaTraceEndpointLower (73 / 80 : ℝ) (183 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (73 / 80 : ℝ) (183 / 200 : ℝ) (6202791 / 1000000 : ℝ) (97404537409 / 15625000000 : ℝ)
    (33160774201 / 10000000000 : ℝ) (23 / 5000000000 : ℝ) (3 / 250000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (73 / 80 : ℝ)) (6202791 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (183 / 200 : ℝ)) (312097 / 125000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (5993907731767 / 5000000000000 : ℝ) (182101 / 100000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_366 :
    (11 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (183 / 200 : ℝ) (367 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (183 / 200 : ℝ) (367 / 400 : ℝ) (6233883 / 1000000 : ℝ) (10024214641 / 1600000000 : ℝ)
    (3336273943209 / 1000000000000 : ℝ) (21 / 5000000000 : ℝ) (11 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (183 / 200 : ℝ)) (6233883 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (367 / 400 : ℝ)) (100121 / 40000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (616885522383 / 512000000000 : ℝ) (1826547 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_367 :
    (1 / 100000 : ℝ) ≤ hpThetaTraceEndpointLower (367 / 400 : ℝ) (23 / 25 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (367 / 400 : ℝ) (23 / 25 : ℝ) (626513 / 100000 : ℝ) (6296541322681 / 1000000000000 : ℝ)
    (209794229089 / 62500000000 : ℝ) (19 / 5000000000 : ℝ) (1 / 100000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (367 / 400 : ℝ)) (626513 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (23 / 25 : ℝ)) (2509291 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (387507103328903 / 320000000000000 : ℝ) (458033 / 250000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_368 :
    (9 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (23 / 25 : ℝ) (369 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (23 / 25 : ℝ) (369 / 400 : ℝ) (3148267 / 500000 : ℝ) (395506405449 / 62500000000 : ℝ)
    (3377365493121 / 1000000000000 : ℝ) (17 / 5000000000 : ℝ) (9 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (23 / 25 : ℝ)) (3148267 / 500000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (369 / 400 : ℝ)) (628893 / 250000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (24341903543287 / 20000000000000 : ℝ) (1837761 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_369 :
    (9 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (369 / 400 : ℝ) (37 / 40 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (369 / 400 : ℝ) (37 / 40 : ℝ) (197753 / 31250 : ℝ) (6359823253161 / 1000000000000 : ℝ)
    (212391017881 / 62500000000 : ℝ) (31 / 10000000000 : ℝ) (9 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (369 / 400 : ℝ)) (197753 / 31250 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (37 / 40 : ℝ)) (2521869 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (391443864949143 / 320000000000000 : ℝ) (460859 / 250000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_370 :
    (1 / 125000 : ℝ) ≤ hpThetaTraceEndpointLower (37 / 40 : ℝ) (371 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (37 / 40 : ℝ) (371 / 400 : ℝ) (1271963 / 200000 : ℝ) (6391699168761 / 1000000000000 : ℝ)
    (3419381610649 / 1000000000000 : ℝ) (7 / 2500000000 : ℝ) (1 / 125000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (37 / 40 : ℝ)) (1271963 / 200000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (371 / 400 : ℝ)) (2528181 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (393427047631943 / 320000000000000 : ℝ) (1849157 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_371 :
    (7 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (371 / 400 : ℝ) (93 / 100 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (371 / 400 : ℝ) (93 / 100 : ℝ) (3195847 / 500000 : ℝ) (64237409401 / 10000000000 : ℝ)
    (3440754175329 / 1000000000000 : ℝ) (1 / 400000000 : ℝ) (7 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (371 / 400 : ℝ)) (3195847 / 500000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (93 / 100 : ℝ)) (253451 / 100000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (3954206792263 / 3200000000000 : ℝ) (1854927 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_372 :
    (3 / 500000 : ℝ) ≤ hpThetaTraceEndpointLower (93 / 100 : ℝ) (373 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (93 / 100 : ℝ) (373 / 400 : ℝ) (1605933 / 250000 : ℝ) (1613984762329 / 250000000000 : ℝ)
    (865590197641 / 250000000000 : ℝ) (23 / 10000000000 : ℝ) (3 / 500000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (93 / 100 : ℝ)) (1605933 / 250000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (373 / 400 : ℝ)) (1270427 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (99356040026727 / 80000000000000 : ℝ) (930371 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_373 :
    (3 / 500000 : ℝ) ≤ hpThetaTraceEndpointLower (373 / 400 : ℝ) (187 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (373 / 400 : ℝ) (187 / 200 : ℝ) (6455931 / 1000000 : ℝ) (1622074790449 / 250000000000 : ℝ)
    (871054489809 / 250000000000 : ℝ) (21 / 10000000000 : ℝ) (3 / 500000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (373 / 400 : ℝ)) (6455931 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (187 / 200 : ℝ)) (1273607 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (99859461798287 / 80000000000000 : ℝ) (933303 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_374 :
    (1 / 200000 : ℝ) ≤ hpThetaTraceEndpointLower (187 / 200 : ℝ) (15 / 16 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (187 / 200 : ℝ) (15 / 16 : ℝ) (6488291 / 1000000 : ℝ) (65208218881 / 10000000000 : ℝ)
    (876580915081 / 250000000000 : ℝ) (19 / 10000000000 : ℝ) (1 / 200000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (187 / 200 : ℝ)) (6488291 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (15 / 16 : ℝ)) (255359 / 100000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (4014617789503 / 3200000000000 : ℝ) (936259 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_375 :
    (1 / 200000 : ℝ) ≤ hpThetaTraceEndpointLower (15 / 16 : ℝ) (47 / 50 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (15 / 16 : ℝ) (47 / 50 : ℝ) (3260407 / 500000 : ℝ) (1638376960081 / 250000000000 : ℝ)
    (551357361 / 156250000 : ℝ) (17 / 10000000000 : ℝ) (1 / 200000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (15 / 16 : ℝ)) (3260407 / 500000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (47 / 50 : ℝ)) (1279991 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (100873998485103 / 80000000000000 : ℝ) (23481 / 12500 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_376 :
    (1 / 250000 : ℝ) ≤ hpThetaTraceEndpointLower (47 / 50 : ℝ) (377 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (47 / 50 : ℝ) (377 / 400 : ℝ) (13107 / 2000 : ℝ) (65863576321 / 10000000000 : ℝ)
    (35513025601 / 10000000000 : ℝ) (3 / 2000000000 : ℝ) (1 / 250000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (47 / 50 : ℝ)) (13107 / 2000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (377 / 400 : ℝ)) (256639 / 100000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (4055405308223 / 3200000000000 : ℝ) (188449 / 100000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_377 :
    (1 / 250000 : ℝ) ≤ hpThetaTraceEndpointLower (377 / 400 : ℝ) (189 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (377 / 400 : ℝ) (189 / 200 : ℝ) (6586349 / 1000000 : ℝ) (1654842969649 / 250000000000 : ℝ)
    (3574183083601 / 1000000000000 : ℝ) (7 / 5000000000 : ℝ) (1 / 250000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (377 / 400 : ℝ)) (6586349 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (189 / 200 : ℝ)) (1286407 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (101898857087887 / 80000000000000 : ℝ) (1890551 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_378 :
    (3 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (189 / 200 : ℝ) (379 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (189 / 200 : ℝ) (379 / 400 : ℝ) (6619363 / 1000000 : ℝ) (1663137799129 / 250000000000 : ℝ)
    (3597322948921 / 1000000000000 : ℝ) (3 / 2500000000 : ℝ) (3 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (189 / 200 : ℝ)) (6619363 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (379 / 400 : ℝ)) (1289627 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (102415181345127 / 80000000000000 : ℝ) (1896661 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_379 :
    (3 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (379 / 400 : ℝ) (19 / 20 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (379 / 400 : ℝ) (19 / 20 : ℝ) (6652543 / 1000000 : ℝ) (66858962041 / 10000000000 : ℝ)
    (3620735369329 / 1000000000000 : ℝ) (11 / 10000000000 : ℝ) (3 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (379 / 400 : ℝ)) (6652543 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (19 / 20 : ℝ)) (258571 / 100000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (4117364608583 / 3200000000000 : ℝ) (1902823 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num


set_option maxHeartbeats 2000000 in
-- Allow the finite endpoint case split to elaborate.
theorem hpThetaFourthCertificateLower_endpoint_batch_18
    (i : ℕ) (hlo : 360 ≤ i) (hi : i < 380) :
    hpThetaFourthCertificateLower i ≤
      hpThetaTraceEndpointLower
        (hpThetaFourthCertificateLeft i)
        (hpThetaFourthCertificateRight i) := by
  -- Apply the resource limit inside each interval case.
  interval_cases i
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_360
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_361
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_362
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_363
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_364
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_365
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_366
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_367
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_368
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_369
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_370
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_371
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_372
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_373
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_374
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_375
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_376
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_377
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_378
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_379
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)

end HodgeProofHP
