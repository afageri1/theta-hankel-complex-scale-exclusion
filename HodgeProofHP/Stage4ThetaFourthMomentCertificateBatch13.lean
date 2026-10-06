import HodgeProofHP.Stage4ThetaFourthMomentCertificateBase

/-! A finite batch of kernel-checked fourth-moment interval certificates. -/

-- Each batch contains twenty explicit exponential certificates.
set_option maxHeartbeats 0
set_option maxRecDepth 10000

noncomputable section

namespace HodgeProofHP

theorem hpThetaFourthCertificate_endpoint_260 :
    (11529 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (13 / 20 : ℝ) (261 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (13 / 20 : ℝ) (261 / 400 : ℝ) (229331 / 62500 : ℝ) (14405040441 / 3906250000 : ℝ)
    (2025267688161 / 1000000000000 : ℝ) (124819 / 10000000000 : ℝ) (11529 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (13 / 20 : ℝ)) (229331 / 62500 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (261 / 400 : ℝ)) (120021 / 62500 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (882126922783 / 1250000000000 : ℝ) (1423119 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_261 :
    (172 / 15625 : ℝ) ≤ hpThetaTraceEndpointLower (261 / 400 : ℝ) (131 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (261 / 400 : ℝ) (131 / 200 : ℝ) (3687689 / 1000000 : ℝ) (3706175570449 / 1000000000000 : ℝ)
    (81299687161 / 40000000000 : ℝ) (58953 / 5000000000 : ℝ) (172 / 15625 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (261 / 400 : ℝ)) (3687689 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (131 / 200 : ℝ)) (1925143 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (226964060938287 / 320000000000000 : ℝ) (285131 / 200000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_262 :
    (2627 / 250000 : ℝ) ≤ hpThetaTraceEndpointLower (131 / 200 : ℝ) (263 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (131 / 200 : ℝ) (263 / 400 : ℝ) (3706173 / 1000000 : ℝ) (931188330361 / 250000000000 : ℝ)
    (2039780947681 / 1000000000000 : ℝ) (111343 / 10000000000 : ℝ) (2627 / 250000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (131 / 200 : ℝ)) (3706173 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (263 / 400 : ℝ)) (964981 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (57027364812743 / 80000000000000 : ℝ) (1428209 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_263 :
    (10027 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (263 / 400 : ℝ) (33 / 50 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (263 / 400 : ℝ) (33 / 50 : ℝ) (14899 / 4000 : ℝ) (3743423952849 / 1000000000000 : ℝ)
    (2047134269961 / 1000000000000 : ℝ) (105113 / 10000000000 : ℝ) (10027 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (263 / 400 : ℝ)) (14899 / 4000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (33 / 50 : ℝ)) (1934793 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (229260709029487 / 320000000000000 : ℝ) (1430781 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_264 :
    (1913 / 200000 : ℝ) ≤ hpThetaTraceEndpointLower (33 / 50 : ℝ) (53 / 80 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (33 / 50 : ℝ) (53 / 80 : ℝ) (3743421 / 1000000 : ℝ) (235136738281 / 62500000000 : ℝ)
    (20545495569 / 10000000000 : ℝ) (19841 / 2000000000 : ℝ) (1913 / 200000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (33 / 50 : ℝ)) (3743421 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (53 / 80 : ℝ)) (484909 / 250000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (14401114511703 / 20000000000000 : ℝ) (143337 / 100000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_265 :
    (4561 / 500000 : ℝ) ≤ hpThetaTraceEndpointLower (53 / 80 : ℝ) (133 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (53 / 80 : ℝ) (133 / 200 : ℝ) (752437 / 200000 : ℝ) (3781045249081 / 1000000000000 : ℝ)
    (2062029944529 / 1000000000000 : ℝ) (93601 / 10000000000 : ℝ) (4561 / 500000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (53 / 80 : ℝ)) (752437 / 200000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (133 / 200 : ℝ)) (1944491 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (231580850692103 / 320000000000000 : ℝ) (1435977 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_266 :
    (8697 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (133 / 200 : ℝ) (267 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (133 / 200 : ℝ) (267 / 400 : ℝ) (3781043 / 1000000 : ℝ) (949999153041 / 250000000000 : ℝ)
    (517393928601 / 250000000000 : ℝ) (88287 / 10000000000 : ℝ) (8697 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (133 / 200 : ℝ)) (3781043 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (267 / 400 : ℝ)) (974679 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (58187446641583 / 80000000000000 : ℝ) (719301 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_267 :
    (8289 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (267 / 400 : ℝ) (67 / 100 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (267 / 400 : ℝ) (67 / 100 : ℝ) (759999 / 200000 : ℝ) (954761540161 / 250000000000 : ℝ)
    (519297508129 / 250000000000 : ℝ) (83249 / 10000000000 : ℝ) (8289 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (267 / 400 : ℝ)) (759999 / 200000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (67 / 100 : ℝ)) (977119 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (58481227030143 / 80000000000000 : ℝ) (720623 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_268 :
    (3949 / 500000 : ℝ) ≤ hpThetaTraceEndpointLower (67 / 100 : ℝ) (269 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (67 / 100 : ℝ) (269 / 400 : ℝ) (3819043 / 1000000 : ℝ) (38381903569 / 10000000000 : ℝ)
    (130304394529 / 62500000000 : ℝ) (3139 / 400000000 : ℝ) (3949 / 500000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (67 / 100 : ℝ)) (3819043 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (269 / 400 : ℝ)) (195913 / 100000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2351059924847 / 3200000000000 : ℝ) (360977 / 250000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_269 :
    (7523 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (269 / 400 : ℝ) (27 / 40 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (269 / 400 : ℝ) (27 / 40 : ℝ) (1919093 / 500000 : ℝ) (3857425625089 / 1000000000000 : ℝ)
    (130788552609 / 62500000000 : ℝ) (36977 / 5000000000 : ℝ) (7523 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (269 / 400 : ℝ)) (1919093 / 500000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (27 / 40 : ℝ)) (1964033 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (236292814380607 / 320000000000000 : ℝ) (361647 / 250000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_270 :
    (1791 / 250000 : ℝ) ≤ hpThetaTraceEndpointLower (27 / 40 : ℝ) (271 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (27 / 40 : ℝ) (271 / 400 : ℝ) (154297 / 40000 : ℝ) (1550705641 / 400000000 : ℝ)
    (32819307921 / 15625000000 : ℝ) (6967 / 1000000000 : ℝ) (1791 / 250000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (27 / 40 : ℝ)) (154297 / 40000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (271 / 400 : ℝ)) (39379 / 20000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (94994455383 / 128000000000 : ℝ) (181161 / 125000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_271 :
    (341 / 50000 : ℝ) ≤ hpThetaTraceEndpointLower (271 / 400 : ℝ) (17 / 25 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (271 / 400 : ℝ) (17 / 25 : ℝ) (96919 / 25000 : ℝ) (974048589721 / 250000000000 : ℝ)
    (527080356009 / 250000000000 : ℝ) (4101 / 625000000 : ℝ) (341 / 50000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (271 / 400 : ℝ)) (96919 / 25000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (17 / 25 : ℝ)) (986939 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (59671311152423 / 80000000000000 : ℝ) (726003 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_272 :
    (649 / 100000 : ℝ) ≤ hpThetaTraceEndpointLower (17 / 25 : ℝ) (273 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (17 / 25 : ℝ) (273 / 400 : ℝ) (3896193 / 1000000 : ℝ) (3915724634761 / 1000000000000 : ℝ)
    (2116277196049 / 1000000000000 : ℝ) (30889 / 5000000000 : ℝ) (649 / 100000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (17 / 25 : ℝ)) (3896193 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (273 / 400 : ℝ)) (1978819 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (239890651989943 / 320000000000000 : ℝ) (1454743 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_273 :
    (3087 / 500000 : ℝ) ≤ hpThetaTraceEndpointLower (273 / 400 : ℝ) (137 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (273 / 400 : ℝ) (137 / 200 : ℝ) (1957861 / 500000 : ℝ) (245959459249 / 62500000000 : ℝ)
    (339889 / 160000 : ℝ) (29073 / 5000000000 : ℝ) (3087 / 500000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (273 / 400 : ℝ)) (1957861 / 500000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (137 / 200 : ℝ)) (495943 / 250000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (15068883432687 / 20000000000000 : ℝ) (583 / 400 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_274 :
    (367 / 62500 : ℝ) ≤ hpThetaTraceEndpointLower (137 / 200 : ℝ) (11 / 16 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (137 / 200 : ℝ) (11 / 16 : ℝ) (78707 / 20000 : ℝ) (988769708161 / 250000000000 : ℝ)
    (133275374761 / 62500000000 : ℝ) (54711 / 10000000000 : ℝ) (367 / 62500 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (137 / 200 : ℝ)) (78707 / 20000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (11 / 16 : ℝ)) (994369 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (60579991614143 / 80000000000000 : ℝ) (365069 / 250000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_275 :
    (2791 / 500000 : ℝ) ≤ hpThetaTraceEndpointLower (11 / 16 : ℝ) (69 / 100 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (11 / 16 : ℝ) (69 / 100 : ℝ) (988769 / 250000 : ℝ) (248431468041 / 62500000000 : ℝ)
    (2140576751041 / 1000000000000 : ℝ) (6433 / 1250000000 : ℝ) (2791 / 500000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (11 / 16 : ℝ)) (988769 / 250000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (69 / 100 : ℝ)) (498429 / 250000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (15221494986583 / 20000000000000 : ℝ) (1463071 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_276 :
    (2653 / 500000 : ℝ) ≤ hpThetaTraceEndpointLower (69 / 100 : ℝ) (277 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (69 / 100 : ℝ) (277 / 400 : ℝ) (3974901 / 1000000 : ℝ) (3994829671849 / 1000000000000 : ℝ)
    (537205441249 / 250000000000 : ℝ) (24197 / 5000000000 : ℝ) (2653 / 500000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (69 / 100 : ℝ)) (3974901 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (277 / 400 : ℝ)) (1998707 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (244774269326487 / 320000000000000 : ℝ) (732943 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_277 :
    (5041 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (277 / 400 : ℝ) (139 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (277 / 400 : ℝ) (139 / 200 : ℝ) (159793 / 40000 : ℝ) (40148537641 / 10000000000 : ℝ)
    (2157141375841 / 1000000000000 : ℝ) (11373 / 2500000000 : ℝ) (5041 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (277 / 400 : ℝ)) (159793 / 40000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (139 / 200 : ℝ)) (200371 / 100000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2460107871383 / 3200000000000 : ℝ) (1468721 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_278 :
    (1197 / 250000 : ℝ) ≤ hpThetaTraceEndpointLower (139 / 200 : ℝ) (279 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (139 / 200 : ℝ) (279 / 400 : ℝ) (4014849 / 1000000 : ℝ) (6455961801 / 1600000000 : ℝ)
    (33836498809 / 15625000000 : ℝ) (42751 / 10000000000 : ℝ) (1197 / 250000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (139 / 200 : ℝ)) (4014849 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (279 / 400 : ℝ)) (80349 / 40000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (395605593463 / 512000000000 : ℝ) (183947 / 125000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_279 :
    (4547 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (279 / 400 : ℝ) (7 / 10 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (279 / 400 : ℝ) (7 / 10 : ℝ) (2017487 / 500000 : ℝ) (4055201145009 / 1000000000000 : ℝ)
    (2174005751401 / 1000000000000 : ℝ) (40163 / 10000000000 : ℝ) (4547 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (279 / 400 : ℝ)) (2017487 / 500000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (7 / 10 : ℝ)) (2013753 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (248502672135567 / 320000000000000 : ℝ) (1474451 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num


set_option maxHeartbeats 2000000 in
-- Allow the finite endpoint case split to elaborate.
theorem hpThetaFourthCertificateLower_endpoint_batch_13
    (i : ℕ) (hlo : 260 ≤ i) (hi : i < 280) :
    hpThetaFourthCertificateLower i ≤
      hpThetaTraceEndpointLower
        (hpThetaFourthCertificateLeft i)
        (hpThetaFourthCertificateRight i) := by
  -- Apply the resource limit inside each interval case.
  interval_cases i
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_260
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_261
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_262
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_263
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_264
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_265
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_266
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_267
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_268
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_269
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_270
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_271
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_272
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_273
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_274
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_275
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_276
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_277
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_278
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_279
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)

end HodgeProofHP
