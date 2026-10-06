import HodgeProofHP.Stage4ThetaFourthMomentCertificateBase

/-! A finite batch of kernel-checked fourth-moment interval certificates. -/

-- Each batch contains twenty explicit exponential certificates.
set_option maxHeartbeats 0
set_option maxRecDepth 10000

noncomputable section

namespace HodgeProofHP

theorem hpThetaFourthCertificate_endpoint_180 :
    (49989 / 250000 : ℝ) ≤ hpThetaTraceEndpointLower (9 / 20 : ℝ) (181 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (9 / 20 : ℝ) (181 / 400 : ℝ) (2459603 / 1000000 : ℝ) (617983082161 / 250000000000 : ℝ)
    (401039758729 / 250000000000 : ℝ) (5200453 / 10000000000 : ℝ) (49989 / 250000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (9 / 20 : ℝ)) (2459603 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (181 / 400 : ℝ)) (786119 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (37807934176143 / 80000000000000 : ℝ) (633277 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_181 :
    (48677 / 250000 : ℝ) ≤ hpThetaTraceEndpointLower (181 / 400 : ℝ) (91 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (181 / 400 : ℝ) (91 / 200 : ℝ) (2471931 / 1000000 : ℝ) (621081119569 / 250000000000 : ℝ)
    (1607953338601 / 1000000000000 : ℝ) (1001509 / 2000000000 : ℝ) (48677 / 250000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (181 / 400 : ℝ)) (2471931 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (91 / 200 : ℝ)) (788087 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (37996860532847 / 80000000000000 : ℝ) (1268051 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_182 :
    (94783 / 500000 : ℝ) ≤ hpThetaTraceEndpointLower (91 / 200 : ℝ) (183 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (91 / 200 : ℝ) (183 / 400 : ℝ) (1242161 / 500000 : ℝ) (2496776054161 / 1000000000000 : ℝ)
    (100735777321 / 62500000000 : ℝ) (1205259 / 2500000000 : ℝ) (94783 / 500000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (91 / 200 : ℝ)) (1242161 / 500000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (183 / 400 : ℝ)) (1580119 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (152746891412143 / 320000000000000 : ℝ) (317389 / 250000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_183 :
    (4613 / 25000 : ℝ) ≤ hpThetaTraceEndpointLower (183 / 400 : ℝ) (23 / 50 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (183 / 400 : ℝ) (23 / 50 : ℝ) (99871 / 40000 : ℝ) (627322609369 / 250000000000 : ℝ)
    (1615621487041 / 1000000000000 : ℝ) (4640513 / 10000000000 : ℝ) (4613 / 25000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (183 / 400 : ℝ)) (99871 / 40000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (23 / 50 : ℝ)) (792037 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (38377574390247 / 80000000000000 : ℝ) (1271071 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_184 :
    (89783 / 500000 : ℝ) ≤ hpThetaTraceEndpointLower (23 / 50 : ℝ) (37 / 80 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (23 / 50 : ℝ) (37 / 80 : ℝ) (250929 / 100000 : ℝ) (1576169401 / 625000000 : ℝ)
    (1619503124409 / 1000000000000 : ℝ) (2232859 / 5000000000 : ℝ) (89783 / 500000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (23 / 50 : ℝ)) (250929 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (37 / 80 : ℝ)) (39701 / 25000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (96423672263 / 200000000000 : ℝ) (1272597 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_185 :
    (21839 / 125000 : ℝ) ≤ hpThetaTraceEndpointLower (37 / 80 : ℝ) (93 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (37 / 80 : ℝ) (93 / 200 : ℝ) (630467 / 250000 : ℝ) (101380470409 / 40000000000 : ℝ)
    (101463272089 / 62500000000 : ℝ) (4296733 / 10000000000 : ℝ) (21839 / 125000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (37 / 80 : ℝ)) (630467 / 250000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (93 / 200 : ℝ)) (318403 / 200000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (6201969635767 / 12800000000000 : ℝ) (318533 / 250000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_186 :
    (84979 / 500000 : ℝ) ≤ hpThetaTraceEndpointLower (93 / 200 : ℝ) (187 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (93 / 200 : ℝ) (187 / 400 : ℝ) (2534509 / 1000000 : ℝ) (159201 / 62500 : ℝ)
    (101709328561 / 62500000000 : ℝ) (2066701 / 5000000000 : ℝ) (84979 / 500000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (93 / 200 : ℝ)) (2534509 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (187 / 400 : ℝ)) (399 / 250 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (4869519 / 10000000 : ℝ) (318919 / 250000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_187 :
    (82647 / 500000 : ℝ) ≤ hpThetaTraceEndpointLower (187 / 400 : ℝ) (47 / 100 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (187 / 400 : ℝ) (47 / 100 : ℝ) (2547213 / 1000000 : ℝ) (102399360001 / 40000000000 : ℝ)
    (1631319027361 / 1000000000000 : ℝ) (397537 / 1000000000 : ℝ) (82647 / 500000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (187 / 400 : ℝ)) (2547213 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (47 / 100 : ℝ)) (319999 / 200000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (6264159680063 / 12800000000000 : ℝ) (1277231 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_188 :
    (20091 / 125000 : ℝ) ≤ hpThetaTraceEndpointLower (47 / 100 : ℝ) (189 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (47 / 100 : ℝ) (189 / 400 : ℝ) (2559981 / 1000000 : ℝ) (160801 / 62500 : ℝ)
    (65412666081 / 40000000000 : ℝ) (38227 / 100000000 : ℝ) (20091 / 125000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (47 / 100 : ℝ)) (2559981 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (189 / 400 : ℝ)) (401 / 250 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (9836713 / 20000000 : ℝ) (255759 / 200000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_189 :
    (4883 / 31250 : ℝ) ≤ hpThetaTraceEndpointLower (189 / 400 : ℝ) (19 / 40 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (189 / 400 : ℝ) (19 / 40 : ℝ) (2572813 / 1000000 : ℝ) (103428489609 / 40000000000 : ℝ)
    (1639344776161 / 1000000000000 : ℝ) (73503 / 200000000 : ℝ) (4883 / 31250 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (189 / 400 : ℝ)) (2572813 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (19 / 40 : ℝ)) (321603 / 200000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (6326994845367 / 12800000000000 : ℝ) (1280369 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_190 :
    (151873 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (19 / 40 : ℝ) (191 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (19 / 40 : ℝ) (191 / 400 : ℝ) (2585709 / 1000000 : ℝ) (1624170601 / 625000000 : ℝ)
    (410851514529 / 250000000000 : ℝ) (3532497 / 10000000000 : ℝ) (151873 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (19 / 40 : ℝ)) (2585709 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (191 / 400 : ℝ)) (40301 / 25000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (99353997863 / 200000000000 : ℝ) (640977 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_191 :
    (73791 / 500000 : ℝ) ≤ hpThetaTraceEndpointLower (191 / 400 : ℝ) (12 / 25 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (191 / 400 : ℝ) (12 / 25 : ℝ) (259867 / 100000 : ℝ) (4178717449 / 1600000000 : ℝ)
    (1647498035401 / 1000000000000 : ℝ) (33947 / 100000000 : ℝ) (73791 / 500000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (191 / 400 : ℝ)) (259867 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (12 / 25 : ℝ)) (64643 / 40000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (255619199287 / 512000000000 : ℝ) (1283549 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_192 :
    (71693 / 500000 : ℝ) ≤ hpThetaTraceEndpointLower (12 / 25 : ℝ) (193 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (12 / 25 : ℝ) (193 / 400 : ℝ) (163231 / 62500 : ℝ) (1640493009 / 625000000 : ℝ)
    (1651618233409 / 1000000000000 : ℝ) (3261709 / 10000000000 : ℝ) (71693 / 500000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (12 / 25 : ℝ)) (163231 / 62500 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (193 / 400 : ℝ)) (40503 / 25000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (100351059567 / 200000000000 : ℝ) (1285153 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_193 :
    (69637 / 500000 : ℝ) ≤ hpThetaTraceEndpointLower (193 / 400 : ℝ) (97 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (193 / 400 : ℝ) (97 / 200 : ℝ) (2624787 / 1000000 : ℝ) (10304483121 / 3906250000 : ℝ)
    (1655774459361 / 1000000000000 : ℝ) (3133149 / 10000000000 : ℝ) (69637 / 500000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (193 / 400 : ℝ)) (2624787 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (97 / 200 : ℝ)) (101511 / 62500 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (630334780373 / 1250000000000 : ℝ) (1286769 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_194 :
    (16907 / 125000 : ℝ) ≤ hpThetaTraceEndpointLower (97 / 200 : ℝ) (39 / 80 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (97 / 200 : ℝ) (39 / 80 : ℝ) (329743 / 125000 : ℝ) (2651168754081 / 1000000000000 : ℝ)
    (414989774809 / 250000000000 : ℝ) (601827 / 2000000000 : ℝ) (16907 / 125000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (97 / 200 : ℝ)) (329743 / 125000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (39 / 80 : ℝ)) (1628241 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (162173631507103 / 320000000000000 : ℝ) (644197 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_195 :
    (3283 / 25000 : ℝ) ≤ hpThetaTraceEndpointLower (39 / 80 : ℝ) (49 / 100 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (39 / 80 : ℝ) (49 / 100 : ℝ) (2651167 / 1000000 : ℝ) (2664458788489 / 1000000000000 : ℝ)
    (1664179980961 / 1000000000000 : ℝ) (2889317 / 10000000000 : ℝ) (3283 / 25000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (39 / 80 : ℝ)) (2651167 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (49 / 100 : ℝ)) (1632317 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (162985903674807 / 320000000000000 : ℝ) (1290031 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_196 :
    (31869 / 250000 : ℝ) ≤ hpThetaTraceEndpointLower (49 / 100 : ℝ) (197 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (49 / 100 : ℝ) (197 / 400 : ℝ) (333057 / 125000 : ℝ) (2677814778409 / 1000000000000 : ℝ)
    (1668429472329 / 1000000000000 : ℝ) (1386897 / 5000000000 : ℝ) (31869 / 250000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (49 / 100 : ℝ)) (333057 / 125000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (197 / 400 : ℝ)) (1636403 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (163802331039767 / 320000000000000 : ℝ) (1291677 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_197 :
    (123717 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (197 / 400 : ℝ) (99 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (197 / 400 : ℝ) (99 / 200 : ℝ) (2677811 / 1000000 : ℝ) (2691236969001 / 1000000000000 : ℝ)
    (418178208889 / 250000000000 : ℝ) (83197 / 312500000 : ℝ) (123717 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (197 / 400 : ℝ)) (2677811 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (99 / 200 : ℝ)) (1640499 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (164622929047063 / 320000000000000 : ℝ) (646667 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_198 :
    (120041 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (99 / 200 : ℝ) (199 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (99 / 200 : ℝ) (199 / 400 : ℝ) (1345617 / 500000 : ℝ) (108189024241 / 40000000000 : ℝ)
    (419257545001 / 250000000000 : ℝ) (510947 / 2000000000 : ℝ) (120041 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (99 / 200 : ℝ)) (1345617 / 500000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (199 / 400 : ℝ)) (328921 / 200000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (6617908527183 / 12800000000000 : ℝ) (647501 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_199 :
    (3639 / 31250 : ℝ) ≤ hpThetaTraceEndpointLower (199 / 400 : ℝ) (1 / 2 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (199 / 400 : ℝ) (1 / 2 : ℝ) (676181 / 250000 : ℝ) (679571058321 / 250000000000 : ℝ)
    (1681381615761 / 1000000000000 : ℝ) (2450977 / 10000000000 : ℝ) (3639 / 31250 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (199 / 400 : ℝ)) (676181 / 250000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (1 / 2 : ℝ)) (824361 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (41569226674223 / 80000000000000 : ℝ) (1296681 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num


set_option maxHeartbeats 2000000 in
-- Allow the finite endpoint case split to elaborate.
theorem hpThetaFourthCertificateLower_endpoint_batch_9
    (i : ℕ) (hlo : 180 ≤ i) (hi : i < 200) :
    hpThetaFourthCertificateLower i ≤
      hpThetaTraceEndpointLower
        (hpThetaFourthCertificateLeft i)
        (hpThetaFourthCertificateRight i) := by
  -- Apply the resource limit inside each interval case.
  interval_cases i
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_180
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_181
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_182
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_183
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_184
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_185
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_186
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_187
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_188
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_189
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_190
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_191
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_192
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_193
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_194
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_195
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_196
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_197
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_198
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_199
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)

end HodgeProofHP
