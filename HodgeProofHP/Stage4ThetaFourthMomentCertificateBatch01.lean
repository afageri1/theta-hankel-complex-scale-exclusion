import HodgeProofHP.Stage4ThetaFourthMomentCertificateBase

/-! A finite batch of kernel-checked fourth-moment interval certificates. -/

-- Each batch contains twenty explicit exponential certificates.
set_option maxHeartbeats 0
set_option maxRecDepth 10000

noncomputable section

namespace HodgeProofHP

theorem hpThetaFourthCertificate_endpoint_20 :
    (847821 / 500000 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 20 : ℝ) (21 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (1 / 20 : ℝ) (21 / 400 : ℝ) (110517 / 100000 : ℝ) (1110711533409 / 1000000000000 : ℝ)
    (310620072889 / 250000000000 : ℝ) (310004403 / 10000000000 : ℝ) (847821 / 500000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (1 / 20 : ℝ)) (110517 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (21 / 400 : ℝ)) (1053903 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (69474826604767 / 320000000000000 : ℝ) (557333 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_21 :
    (1691389 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (21 / 400 : ℝ) (11 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (21 / 400 : ℝ) (11 / 200 : ℝ) (111071 / 100000 : ℝ) (1116278884681 / 1000000000000 : ℝ)
    (310936718689 / 250000000000 : ℝ) (304991657 / 10000000000 : ℝ) (1691389 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (21 / 400 : ℝ)) (111071 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (11 / 200 : ℝ)) (1056541 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (69800569734903 / 320000000000000 : ℝ) (557617 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_22 :
    (1687009 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (11 / 200 : ℝ) (23 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (11 / 200 : ℝ) (23 / 400 : ℝ) (558139 / 500000 : ℝ) (280468745649 / 250000000000 : ℝ)
    (77813660401 / 62500000000 : ℝ) (4688207 / 156250000 : ℝ) (1687009 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (11 / 200 : ℝ)) (558139 / 500000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (23 / 400 : ℝ)) (529593 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (17532030975887 / 80000000000000 : ℝ) (278951 / 250000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_23 :
    (336471 / 200000 : ℝ) ≤ hpThetaTraceEndpointLower (23 / 400 : ℝ) (3 / 50 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (23 / 400 : ℝ) (3 / 50 : ℝ) (1121873 / 1000000 : ℝ) (1127497814569 / 1000000000000 : ℝ)
    (1246302071641 / 1000000000000 : ℝ) (147569611 / 5000000000 : ℝ) (336471 / 200000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (23 / 400 : ℝ)) (1121873 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (3 / 50 : ℝ)) (1061837 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (70457362317847 / 320000000000000 : ℝ) (1116379 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_24 :
    (1677577 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (3 / 50 : ℝ) (1 / 16 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (3 / 50 : ℝ) (1 / 16 : ℝ) (140937 / 125000 : ℝ) (45325984201 / 40000000000 : ℝ)
    (77974419121 / 62500000000 : ℝ) (58059849 / 2000000000 : ℝ) (1677577 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (3 / 50 : ℝ)) (140937 / 125000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (1 / 16 : ℝ)) (212899 / 200000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2831537004663 / 12800000000000 : ℝ) (279239 / 250000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_25 :
    (334517 / 200000 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 16 : ℝ) (13 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (1 / 16 : ℝ) (13 / 200 : ℝ) (283287 / 250000 : ℝ) (711769041 / 625000000 : ℝ)
    (1248888946369 / 1000000000000 : ℝ) (142754187 / 5000000000 : ℝ) (334517 / 200000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (1 / 16 : ℝ)) (283287 / 250000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (13 / 200 : ℝ)) (26679 / 25000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (44450824583 / 200000000000 : ℝ) (1117537 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_26 :
    (833689 / 500000 : ℝ) ≤ hpThetaTraceEndpointLower (13 / 200 : ℝ) (27 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (13 / 200 : ℝ) (27 / 400 : ℝ) (284707 / 250000 : ℝ) (1144538368561 / 1000000000000 : ℝ)
    (312549201721 / 250000000000 : ℝ) (280766853 / 10000000000 : ℝ) (833689 / 500000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (13 / 200 : ℝ)) (284707 / 250000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (27 / 400 : ℝ)) (1069831 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (71455917219343 / 320000000000000 : ℝ) (559061 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_27 :
    (332401 / 200000 : ℝ) ≤ hpThetaTraceEndpointLower (27 / 400 : ℝ) (7 / 100 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (27 / 400 : ℝ) (7 / 100 : ℝ) (143067 / 125000 : ℝ) (1150275555081 / 1000000000000 : ℝ)
    (12515120641 / 10000000000 : ℝ) (276082801 / 10000000000 : ℝ) (332401 / 200000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (27 / 400 : ℝ)) (143067 / 125000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (7 / 100 : ℝ)) (1072509 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (71792359970103 / 320000000000000 : ℝ) (111871 / 100000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_28 :
    (1656473 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (7 / 100 : ℝ) (29 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (7 / 100 : ℝ) (29 / 400 : ℝ) (1150273 / 1000000 : ℝ) (1156039987249 / 1000000000000 : ℝ)
    (1252834728601 / 1000000000000 : ℝ) (271456011 / 10000000000 : ℝ) (1656473 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (7 / 100 : ℝ)) (1150273 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (29 / 400 : ℝ)) (1075193 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (72130519196687 / 320000000000000 : ℝ) (1119301 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_29 :
    (103171 / 62500 : ℝ) ≤ hpThetaTraceEndpointLower (29 / 400 : ℝ) (3 / 40 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (29 / 400 : ℝ) (3 / 40 : ℝ) (1156039 / 1000000 : ℝ) (46473442929 / 40000000000 : ℝ)
    (19596360169 / 15625000000 : ℝ) (66719659 / 2500000000 : ℝ) (103171 / 62500 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (29 / 400 : ℝ)) (1156039 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (3 / 40 : ℝ)) (215577 / 200000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2898826904527 / 12800000000000 : ℝ) (139987 / 125000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_30 :
    (411211 / 250000 : ℝ) ≤ hpThetaTraceEndpointLower (3 / 40 : ℝ) (31 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (3 / 40 : ℝ) (31 / 400 : ℝ) (580917 / 500000 : ℝ) (1167659619889 / 1000000000000 : ℝ)
    (313876701009 / 250000000000 : ℝ) (262358337 / 10000000000 : ℝ) (411211 / 250000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (3 / 40 : ℝ)) (580917 / 500000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (31 / 400 : ℝ)) (1080583 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (72812556053007 / 320000000000000 : ℝ) (560247 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_31 :
    (1638749 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (31 / 400 : ℝ) (2 / 25 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (31 / 400 : ℝ) (2 / 25 : ℝ) (1167657 / 1000000 : ℝ) (18336138921 / 15625000000 : ℝ)
    (19638378769 / 15625000000 : ℝ) (128943753 / 5000000000 : ℝ) (1638749 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (31 / 400 : ℝ)) (1167657 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (2 / 25 : ℝ)) (135411 / 125000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (1143067377023 / 5000000000000 : ℝ) (140137 / 125000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_32 :
    (81623 / 50000 : ℝ) ≤ hpThetaTraceEndpointLower (2 / 25 : ℝ) (33 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (2 / 25 : ℝ) (33 / 400 : ℝ) (117351 / 100000 : ℝ) (1179393828001 / 1000000000000 : ℝ)
    (314553844201 / 250000000000 : ℝ) (63366569 / 2500000000 : ℝ) (81623 / 50000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (2 / 25 : ℝ)) (117351 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (33 / 400 : ℝ)) (1085999 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (73501811164063 / 320000000000000 : ℝ) (560851 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_33 :
    (813013 / 500000 : ℝ) ≤ hpThetaTraceEndpointLower (33 / 400 : ℝ) (17 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (33 / 400 : ℝ) (17 / 200 : ℝ) (1179393 / 1000000 : ℝ) (296326720881 / 250000000000 : ℝ)
    (1259581980721 / 1000000000000 : ℝ) (124550931 / 5000000000 : ℝ) (813013 / 500000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (33 / 400 : ℝ)) (1179393 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (17 / 200 : ℝ)) (544359 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (18462333415503 / 80000000000000 : ℝ) (1122311 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_34 :
    (1619397 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (17 / 200 : ℝ) (7 / 80 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (17 / 200 : ℝ) (7 / 80 : ℝ) (148163 / 125000 : ℝ) (1191247822249 / 1000000000000 : ℝ)
    (78809894361 / 62500000000 : ℝ) (244787001 / 10000000000 : ℝ) (1619397 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (17 / 200 : ℝ)) (148163 / 125000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (7 / 80 : ℝ)) (1091443 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (74198612801687 / 320000000000000 : ℝ) (280731 / 250000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_35 :
    (1612631 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (7 / 80 : ℝ) (9 / 100 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (7 / 80 : ℝ) (9 / 100 : ℝ) (595623 / 500000 : ℝ) (1915550289 / 1600000000 : ℝ)
    (3155855329 / 2500000000 : ℝ) (240528621 / 10000000000 : ℝ) (1612631 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (7 / 80 : ℝ)) (595623 / 500000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (9 / 100 : ℝ)) (43767 / 40000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (119279668207 / 512000000000 : ℝ) (56177 / 50000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_36 :
    (1605679 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (9 / 100 : ℝ) (37 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (9 / 100 : ℝ) (37 / 400 : ℝ) (1197217 / 1000000 : ℝ) (300805080849 / 250000000000 : ℝ)
    (12341169 / 9765625 : ℝ) (47263937 / 2000000000 : ℝ) (1605679 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (9 / 100 : ℝ)) (1197217 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (37 / 400 : ℝ)) (548457 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (18725720093487 / 80000000000000 : ℝ) (3513 / 3125 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_37 :
    (1598547 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (37 / 400 : ℝ) (19 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (37 / 400 : ℝ) (19 / 200 : ℝ) (601609 / 500000 : ℝ) (1209249916281 / 1000000000000 : ℝ)
    (4941949401 / 3906250000 : ℝ) (232160239 / 10000000000 : ℝ) (1598547 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (37 / 400 : ℝ)) (601609 / 500000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (19 / 200 : ℝ)) (1099659 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (75257744725703 / 320000000000000 : ℝ) (70299 / 62500 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_38 :
    (795641 / 500000 : ℝ) ≤ hpThetaTraceEndpointLower (19 / 200 : ℝ) (39 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (19 / 200 : ℝ) (39 / 400 : ℝ) (1209249 / 1000000 : ℝ) (75957013609 / 62500000000 : ℝ)
    (1266549918921 / 1000000000000 : ℝ) (45611359 / 2000000000 : ℝ) (795641 / 500000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (19 / 200 : ℝ)) (1209249 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (39 / 400 : ℝ)) (275603 / 250000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (4725916857367 / 20000000000000 : ℝ) (1125411 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_39 :
    (1583843 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (39 / 400 : ℝ) (1 / 10 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (39 / 400 : ℝ) (1 / 10 : ℝ) (121531 / 100000 : ℝ) (1221402939241 / 1000000000000 : ℝ)
    (316992646441 / 250000000000 : ℝ) (2800033 / 125000000 : ℝ) (1583843 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (39 / 400 : ℝ)) (121531 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (1 / 10 : ℝ)) (1105171 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (75973385172183 / 320000000000000 : ℝ) (563021 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num


set_option maxHeartbeats 2000000 in
-- Allow the finite endpoint case split to elaborate.
theorem hpThetaFourthCertificateLower_endpoint_batch_1
    (i : ℕ) (hlo : 20 ≤ i) (hi : i < 40) :
    hpThetaFourthCertificateLower i ≤
      hpThetaTraceEndpointLower
        (hpThetaFourthCertificateLeft i)
        (hpThetaFourthCertificateRight i) := by
  -- Apply the resource limit inside each interval case.
  interval_cases i
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_20
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_21
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_22
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_23
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_24
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_25
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_26
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_27
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_28
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_29
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_30
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_31
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_32
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_33
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_34
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_35
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_36
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_37
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_38
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_39
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)

end HodgeProofHP
