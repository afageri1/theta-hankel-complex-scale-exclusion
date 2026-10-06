import HodgeProofHP.Stage4ThetaFourthMomentCertificateBase

/-! A finite batch of kernel-checked fourth-moment interval certificates. -/

-- Each batch contains twenty explicit exponential certificates.
set_option maxHeartbeats 0
set_option maxRecDepth 10000

noncomputable section

namespace HodgeProofHP

theorem hpThetaFourthCertificate_endpoint_380 :
    (3 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (19 / 20 : ℝ) (381 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (19 / 20 : ℝ) (381 / 400 : ℝ) (6685889 / 1000000 : ℝ) (6719412705489 / 1000000000000 : ℝ)
    (3644422267369 / 1000000000000 : ℝ) (1 / 1000000000 : ℝ) (3 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (19 / 20 : ℝ)) (6685889 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (381 / 400 : ℝ)) (2592183 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (413823000445807 / 320000000000000 : ℝ) (1909037 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_381 :
    (1 / 500000 : ℝ) ≤ hpThetaTraceEndpointLower (381 / 400 : ℝ) (191 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (381 / 400 : ℝ) (191 / 200 : ℝ) (3359701 / 500000 : ℝ) (6753090966241 / 1000000000000 : ℝ)
    (3668377920601 / 1000000000000 : ℝ) (9 / 10000000000 : ℝ) (1 / 500000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (381 / 400 : ℝ)) (3359701 / 500000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (191 / 200 : ℝ)) (2598671 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (415919730873183 / 320000000000000 : ℝ) (1915301 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_382 :
    (1 / 500000 : ℝ) ≤ hpThetaTraceEndpointLower (191 / 200 : ℝ) (383 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (191 / 200 : ℝ) (383 / 400 : ℝ) (6753083 / 1000000 : ℝ) (106045968609 / 15625000000 : ℝ)
    (3692619581161 / 1000000000000 : ℝ) (1 / 1250000000 : ℝ) (1 / 500000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (191 / 200 : ℝ)) (6753083 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (383 / 400 : ℝ)) (325647 / 125000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (6531677272367 / 5000000000000 : ℝ) (1921619 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_383 :
    (1 / 500000 : ℝ) ≤ hpThetaTraceEndpointLower (383 / 400 : ℝ) (24 / 25 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (383 / 400 : ℝ) (24 / 25 : ℝ) (1696733 / 250000 : ℝ) (6820961219809 / 1000000000000 : ℝ)
    (3717141584121 / 1000000000000 : ℝ) (7 / 10000000000 : ℝ) (1 / 500000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (383 / 400 : ℝ)) (1696733 / 250000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (24 / 25 : ℝ)) (2611697 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (420145556847967 / 320000000000000 : ℝ) (1927989 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_384 :
    (1 / 500000 : ℝ) ≤ hpThetaTraceEndpointLower (24 / 25 : ℝ) (77 / 80 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (24 / 25 : ℝ) (77 / 80 : ℝ) (852619 / 125000 : ℝ) (1713787319689 / 250000000000 : ℝ)
    (3741953654569 / 1000000000000 : ℝ) (3 / 5000000000 : ℝ) (1 / 500000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (24 / 25 : ℝ)) (852619 / 125000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (77 / 80 : ℝ)) (1309117 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (105568601140407 / 80000000000000 : ℝ) (1934413 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_385 :
    (1 / 500000 : ℝ) ≤ hpThetaTraceEndpointLower (77 / 80 : ℝ) (193 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (77 / 80 : ℝ) (193 / 200 : ℝ) (3427571 / 500000 : ℝ) (430594502809 / 62500000000 : ℝ)
    (235441359729 / 62500000000 : ℝ) (3 / 5000000000 : ℝ) (1 / 500000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (77 / 80 : ℝ)) (3427571 / 500000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (193 / 200 : ℝ)) (656197 / 250000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (26525891176967 / 20000000000000 : ℝ) (485223 / 250000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_386 :
    (1 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (193 / 200 : ℝ) (387 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (193 / 200 : ℝ) (387 / 400 : ℝ) (6889503 / 1000000 : ℝ) (1731011231041 / 250000000000 : ℝ)
    (6067942609 / 1600000000 : ℝ) (1 / 2000000000 : ℝ) (1 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (193 / 200 : ℝ)) (6889503 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (387 / 400 : ℝ)) (1315679 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (106641207555583 / 80000000000000 : ℝ) (77897 / 40000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_387 :
    (1 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (387 / 400 : ℝ) (97 / 100 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (387 / 400 : ℝ) (97 / 100 : ℝ) (6924037 / 1000000 : ℝ) (278350152921 / 40000000000 : ℝ)
    (3818166804169 / 1000000000000 : ℝ) (1 / 2500000000 : ℝ) (1 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (387 / 400 : ℝ)) (6924037 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (97 / 100 : ℝ)) (527589 / 200000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (17149059634023 / 12800000000000 : ℝ) (1954013 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_388 :
    (1 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (97 / 100 : ℝ) (389 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (97 / 100 : ℝ) (389 / 400 : ℝ) (869843 / 125000 : ℝ) (437102132769 / 62500000000 : ℝ)
    (3844175871649 / 1000000000000 : ℝ) (1 / 2500000000 : ℝ) (1 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (97 / 100 : ℝ)) (869843 / 125000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (389 / 400 : ℝ)) (661137 / 250000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (26931184364447 / 20000000000000 : ℝ) (1960657 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_389 :
    (1 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (389 / 400 : ℝ) (39 / 40 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (389 / 400 : ℝ) (39 / 40 : ℝ) (874203 / 125000 : ℝ) (6863956801 / 976562500 : ℝ)
    (3870501434881 / 1000000000000 : ℝ) (3 / 10000000000 : ℝ) (1 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (389 / 400 : ℝ)) (874203 / 125000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (39 / 40 : ℝ)) (82849 / 31250 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (845864416301 / 625000000000 : ℝ) (1967359 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_390 :
    (1 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (39 / 40 : ℝ) (391 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (39 / 40 : ℝ) (391 / 400 : ℝ) (175717 / 25000 : ℝ) (441495131401 / 62500000000 : ℝ)
    (243570873841 / 62500000000 : ℝ) (3 / 10000000000 : ℝ) (1 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (39 / 40 : ℝ)) (175717 / 25000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (391 / 400 : ℝ)) (664451 / 250000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (27204818278263 / 20000000000000 : ℝ) (493529 / 250000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_391 :
    (1 / 1000000 : ℝ) ≤ hpThetaTraceEndpointLower (391 / 400 : ℝ) (49 / 50 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (391 / 400 : ℝ) (49 / 50 : ℝ) (7063911 / 1000000 : ℝ) (7099331104849 / 1000000000000 : ℝ)
    (245255724289 / 62500000000 : ℝ) (3 / 10000000000 : ℝ) (1 / 1000000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (391 / 400 : ℝ)) (7063911 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (49 / 50 : ℝ)) (2664457 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (437482859605487 / 320000000000000 : ℝ) (495233 / 250000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_392 :
    (0 / 1 : ℝ) ≤ hpThetaTraceEndpointLower (49 / 50 : ℝ) (393 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (49 / 50 : ℝ) (393 / 400 : ℝ) (7099319 / 1000000 : ℝ) (1783728526969 / 250000000000 : ℝ)
    (158054748721 / 40000000000 : ℝ) (1 / 5000000000 : ℝ) (0 / 1 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (49 / 50 : ℝ)) (7099319 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (393 / 400 : ℝ)) (1335563 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (109924897199047 / 80000000000000 : ℝ) (397561 / 200000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_393 :
    (0 / 1 : ℝ) ≤ hpThetaTraceEndpointLower (393 / 400 : ℝ) (197 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (393 / 400 : ℝ) (197 / 200 : ℝ) (891863 / 125000 : ℝ) (448167319209 / 62500000000 : ℝ)
    (3978975699169 / 1000000000000 : ℝ) (1 / 5000000000 : ℝ) (0 / 1 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (393 / 400 : ℝ)) (891863 / 125000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (197 / 200 : ℝ)) (669453 / 250000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (27620478610167 / 20000000000000 : ℝ) (1994737 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_394 :
    (0 / 1 : ℝ) ≤ hpThetaTraceEndpointLower (197 / 200 : ℝ) (79 / 80 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (197 / 200 : ℝ) (79 / 80 : ℝ) (1792667 / 250000 : ℝ) (288264831409 / 40000000000 : ℝ)
    (4006918989441 / 1000000000000 : ℝ) (1 / 5000000000 : ℝ) (0 / 1 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (197 / 200 : ℝ)) (1792667 / 250000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (79 / 80 : ℝ)) (536903 / 200000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (17766684378767 / 12800000000000 : ℝ) (2001729 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_395 :
    (0 / 1 : ℝ) ≤ hpThetaTraceEndpointLower (79 / 80 : ℝ) (99 / 100 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (79 / 80 : ℝ) (99 / 100 : ℝ) (7206611 / 1000000 : ℝ) (289709833009 / 40000000000 : ℝ)
    (1008801280881 / 250000000000 : ℝ) (1 / 5000000000 : ℝ) (0 / 1 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (79 / 80 : ℝ)) (7206611 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (99 / 100 : ℝ)) (538247 / 200000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (17856719479567 / 12800000000000 : ℝ) (1004391 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_396 :
    (0 / 1 : ℝ) ≤ hpThetaTraceEndpointLower (99 / 100 : ℝ) (397 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (99 / 100 : ℝ) (397 / 400 : ℝ) (3621367 / 500000 : ℝ) (7279047516841 / 1000000000000 : ℝ)
    (1015957154809 / 250000000000 : ℝ) (1 / 10000000000 : ℝ) (0 / 1 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (99 / 100 : ℝ)) (3621367 / 500000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (397 / 400 : ℝ)) (2697971 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (448679993560983 / 320000000000000 : ℝ) (1007947 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_397 :
    (0 / 1 : ℝ) ≤ hpThetaTraceEndpointLower (397 / 400 : ℝ) (199 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (397 / 400 : ℝ) (199 / 200 : ℝ) (3639519 / 500000 : ℝ) (11704859721 / 1600000000 : ℝ)
    (4092808178761 / 1000000000000 : ℝ) (1 / 10000000000 : ℝ) (0 / 1 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (397 / 400 : ℝ)) (3639519 / 500000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (199 / 200 : ℝ)) (108189 / 40000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (721526162423 / 512000000000 : ℝ) (2023069 / 1000000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_398 :
    (0 / 1 : ℝ) ≤ hpThetaTraceEndpointLower (199 / 200 : ℝ) (399 / 400 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (199 / 200 : ℝ) (399 / 400 : ℝ) (1828881 / 250000 : ℝ) (294088205401 / 40000000000 : ℝ)
    (164885535721 / 40000000000 : ℝ) (1 / 10000000000 : ℝ) (0 / 1 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (199 / 200 : ℝ)) (1828881 / 250000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (399 / 400 : ℝ)) (542299 / 200000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (18129556940263 / 12800000000000 : ℝ) (406061 / 200000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaFourthCertificate_endpoint_399 :
    (0 / 1 : ℝ) ≤ hpThetaTraceEndpointLower (399 / 400 : ℝ) (1 / 1 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (399 / 400 : ℝ) (1 / 1 : ℝ) (7352193 / 1000000 : ℝ) (1847264257881 / 250000000000 : ℝ)
    (259489378801 / 62500000000 : ℝ) (1 / 10000000000 : ℝ) (0 / 1 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (399 / 400 : ℝ)) (7352193 / 1000000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · have h := hpThetaFourthCertificate_exp_upper_square
      (2 * (1 / 1 : ℝ)) (1359141 / 500000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · have h := hpThetaFourthCertificate_exp_upper_square
      (113883898246503 / 80000000000000 : ℝ) (509401 / 250000 : ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num


set_option maxHeartbeats 2000000 in
-- Allow the finite endpoint case split to elaborate.
theorem hpThetaFourthCertificateLower_endpoint_batch_19
    (i : ℕ) (hlo : 380 ≤ i) (hi : i < 400) :
    hpThetaFourthCertificateLower i ≤
      hpThetaTraceEndpointLower
        (hpThetaFourthCertificateLeft i)
        (hpThetaFourthCertificateRight i) := by
  -- Apply the resource limit inside each interval case.
  interval_cases i
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_380
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_381
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_382
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_383
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_384
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_385
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_386
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_387
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_388
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_389
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_390
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_391
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_392
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_393
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_394
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_395
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_396
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_397
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_398
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)
  · set_option maxHeartbeats 2000000 in
    exact (by
      have h := hpThetaFourthCertificate_endpoint_399
      norm_num [hpThetaFourthCertificateLeft,
        hpThetaFourthCertificateRight, hpThetaFourthCertificateLower] at h ⊢
      exact h)

end HodgeProofHP
