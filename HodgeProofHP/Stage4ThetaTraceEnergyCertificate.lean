import HodgeProofHP.Stage4ThetaTraceFiniteEnergySum
import HodgeProofHP.Stage4ThetaTraceExpCertificates
import HodgeProofHP.Stage4ThetaTraceExpScaling

/-!
Rational certificates for a lower bound on the first trace energy.
Every numerical inequality below is checked by Lean.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace HodgeProofHP

open MeasureTheory

theorem hpThetaTrace_rational_endpoint_certificate
    (l r L U V W q : ℝ)
    (hL0 : 0 ≤ L)
    (hL : L ≤ Real.exp (2 * l))
    (hU : Real.exp (2 * r) ≤ U)
    (hV0 : 0 ≤ V)
    (hW0 : 0 ≤ W)
    (hV : Real.exp (((63 / 20 : ℝ) * U - l / 2) / 16) ≤ V)
    (hWV : W * V ^ 16 ≤ 1)
    (ha : 3 ≤ (157 / 50 : ℝ) * L)
    (hq : q ≤
      (4 * ((157 / 50 : ℝ) * L) ^ 2 -
        6 * ((157 / 50 : ℝ) * L)) * (2 * W)) :
    q ≤ hpThetaTraceEndpointLower l r := by
  have hpiL : (157 / 50 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d2
    linarith
  have hpiU : Real.pi ≤ (63 / 20 : ℝ) := by
    have h := Real.pi_lt_d2
    linarith
  have hsmall :
      (157 / 50 : ℝ) * L ≤ Real.pi * Real.exp (2 * l) := by
    exact mul_le_mul hpiL hL hL0 (le_trans (by norm_num) hpiL)
  have hlarge :
      Real.pi * Real.exp (2 * r) ≤ (63 / 20 : ℝ) * U := by
    exact mul_le_mul hpiU hU
      (le_of_lt (Real.exp_pos _)) (by norm_num)
  have hp :
      4 * ((157 / 50 : ℝ) * L) ^ 2 -
          6 * ((157 / 50 : ℝ) * L) ≤
        4 * (Real.pi * Real.exp (2 * l)) ^ 2 -
          6 * (Real.pi * Real.exp (2 * l)) :=
    hpThetaTrace_scalar_polynomial_mono _ _ ha hsmall
  have hp0 :
      0 ≤ 4 * ((157 / 50 : ℝ) * L) ^ 2 -
        6 * ((157 / 50 : ℝ) * L) := by
    nlinarith [sq_nonneg ((157 / 50 : ℝ) * L - 3)]
  have hdecay :
      W ≤ Real.exp (-((63 / 20 : ℝ) * U - l / 2)) := by
    have h := hpThetaTrace_exp_neg_nat_mul_lower
      (((63 / 20 : ℝ) * U - l / 2) / 16)
      V W 16 hV0 hW0 hV hWV
    norm_num only [Nat.cast_ofNat] at h
    have heq :
        -((16 : ℝ) * (((63 / 20 : ℝ) * U - l / 2) / 16)) =
        -((63 / 20 : ℝ) * U - l / 2) := by ring
    rw [heq] at h
    exact h
  have hexp :
      W ≤ Real.exp (l / 2 - Real.pi * Real.exp (2 * r)) := by
    apply le_trans hdecay
    apply Real.exp_le_exp.mpr
    linarith
  have hpActual0 :
      0 ≤ 4 * (Real.pi * Real.exp (2 * l)) ^ 2 -
        6 * (Real.pi * Real.exp (2 * l)) :=
    le_trans hp0 hp
  unfold hpThetaTraceEndpointLower
  exact le_trans hq
    (mul_le_mul hp
      (mul_le_mul_of_nonneg_left hexp (by norm_num))
      (mul_nonneg (by norm_num) hW0) hpActual0)


theorem hpThetaTrace_energy_endpoint_0 :
    (8551 / 5000 : ℝ) ≤ hpThetaTraceEndpointLower (0 / 1 : ℝ) (1 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (0 / 1 : ℝ) (1 / 200 : ℝ) (1 / 1 : ℝ) (50503 / 50000 : ℝ)
    (122001 / 100000 : ℝ) (830263 / 20000000 : ℝ) (8551 / 5000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (0 / 1 : ℝ)) (1 / 1 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (1 / 200 : ℝ)) (50503 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((3181689 / 1000000 : ℝ) / 16) (122001 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_1 :
    (8547 / 5000 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 200 : ℝ) (1 / 100 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (1 / 200 : ℝ) (1 / 100 : ℝ) (20201 / 20000 : ℝ) (102021 / 100000 : ℝ)
    (61113 / 50000 : ℝ) (4030717 / 100000000 : ℝ) (8547 / 5000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (1 / 200 : ℝ)) (20201 / 20000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (1 / 100 : ℝ)) (102021 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((6422323 / 2000000 : ℝ) / 16) (61113 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_2 :
    (8539 / 5000 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 100 : ℝ) (3 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (1 / 100 : ℝ) (3 / 200 : ℝ) (5101 / 5000 : ℝ) (51523 / 50000 : ℝ)
    (61227 / 50000 : ℝ) (1956151 / 50000000 : ℝ) (8539 / 5000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (1 / 100 : ℝ)) (5101 / 5000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (3 / 200 : ℝ)) (51523 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((3240949 / 1000000 : ℝ) / 16) (61227 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_3 :
    (8527 / 5000 : ℝ) ≤ hpThetaTraceEndpointLower (3 / 200 : ℝ) (1 / 50 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (3 / 200 : ℝ) (1 / 50 : ℝ) (20609 / 20000 : ℝ) (52041 / 50000 : ℝ)
    (24537 / 20000 : ℝ) (379609 / 10000000 : ℝ) (8527 / 5000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (3 / 200 : ℝ)) (20609 / 20000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (1 / 50 : ℝ)) (52041 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((3271083 / 1000000 : ℝ) / 16) (24537 / 20000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_4 :
    (17023 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 50 : ℝ) (1 / 40 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (1 / 50 : ℝ) (1 / 40 : ℝ) (104081 / 100000 : ℝ) (13141 / 12500 : ℝ)
    (61459 / 50000 : ℝ) (184129 / 5000000 : ℝ) (17023 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (1 / 50 : ℝ)) (104081 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (1 / 40 : ℝ)) (13141 / 12500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((825383 / 250000 : ℝ) / 16) (61459 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_5 :
    (8491 / 5000 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 40 : ℝ) (3 / 100 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (1 / 40 : ℝ) (3 / 100 : ℝ) (105127 / 100000 : ℝ) (13273 / 12500 : ℝ)
    (24631 / 20000 : ℝ) (3570813 / 100000000 : ℝ) (8491 / 5000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (1 / 40 : ℝ)) (105127 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (3 / 100 : ℝ)) (13273 / 12500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((416537 / 125000 : ℝ) / 16) (24631 / 20000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_6 :
    (16933 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (3 / 100 : ℝ) (7 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (3 / 100 : ℝ) (7 / 200 : ℝ) (106183 / 100000 : ℝ) (107251 / 100000 : ℝ)
    (24679 / 20000 : ℝ) (1730649 / 50000000 : ℝ) (16933 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (3 / 100 : ℝ)) (106183 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (7 / 200 : ℝ)) (107251 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((6726813 / 2000000 : ℝ) / 16) (24679 / 20000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_7 :
    (8439 / 5000 : ℝ) ≤ hpThetaTraceEndpointLower (7 / 200 : ℝ) (1 / 25 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (7 / 200 : ℝ) (1 / 25 : ℝ) (429 / 400 : ℝ) (108329 / 100000 : ℝ)
    (123637 / 100000 : ℝ) (134179 / 4000000 : ℝ) (8439 / 5000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (7 / 200 : ℝ)) (429 / 400 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (1 / 25 : ℝ)) (108329 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((6789727 / 2000000 : ℝ) / 16) (123637 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_8 :
    (16813 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 25 : ℝ) (9 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (1 / 25 : ℝ) (9 / 200 : ℝ) (13541 / 12500 : ℝ) (54709 / 50000 : ℝ)
    (123883 / 100000 : ℝ) (324947 / 10000000 : ℝ) (16813 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (1 / 25 : ℝ)) (13541 / 12500 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (9 / 200 : ℝ)) (54709 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((3426667 / 1000000 : ℝ) / 16) (123883 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_9 :
    (16739 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (9 / 200 : ℝ) (1 / 20 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (9 / 200 : ℝ) (1 / 20 : ℝ) (109417 / 100000 : ℝ) (55259 / 50000 : ℝ)
    (124133 / 100000 : ℝ) (3146327 / 100000000 : ℝ) (16739 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (9 / 200 : ℝ)) (109417 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (1 / 20 : ℝ)) (55259 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((3458817 / 1000000 : ℝ) / 16) (124133 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_10 :
    (833 / 500 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 20 : ℝ) (11 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (1 / 20 : ℝ) (11 / 200 : ℝ) (110517 / 100000 : ℝ) (27907 / 25000 : ℝ)
    (24877 / 20000 : ℝ) (3045873 / 100000000 : ℝ) (833 / 500 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (1 / 20 : ℝ)) (110517 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (11 / 200 : ℝ)) (27907 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((1745641 / 500000 : ℝ) / 16) (24877 / 20000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_11 :
    (16573 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (11 / 200 : ℝ) (3 / 50 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (11 / 200 : ℝ) (3 / 50 : ℝ) (111627 / 100000 : ℝ) (451 / 400 : ℝ)
    (779 / 625 : ℝ) (736921 / 25000000 : ℝ) (16573 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (11 / 200 : ℝ)) (111627 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (3 / 50 : ℝ)) (451 / 400 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((28193 / 8000 : ℝ) / 16) (779 / 625 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_12 :
    (16477 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (3 / 50 : ℝ) (13 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (3 / 50 : ℝ) (13 / 200 : ℝ) (112749 / 100000 : ℝ) (113883 / 100000 : ℝ)
    (124899 / 100000 : ℝ) (2851389 / 100000000 : ℝ) (16477 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (3 / 50 : ℝ)) (112749 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (13 / 200 : ℝ)) (113883 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((7114629 / 2000000 : ℝ) / 16) (124899 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_13 :
    (8187 / 5000 : ℝ) ≤ hpThetaTraceEndpointLower (13 / 200 : ℝ) (7 / 100 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (13 / 200 : ℝ) (7 / 100 : ℝ) (56941 / 50000 : ℝ) (28757 / 25000 : ℝ)
    (125161 / 100000 : ℝ) (2757373 / 100000000 : ℝ) (8187 / 5000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (13 / 200 : ℝ)) (56941 / 50000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (7 / 100 : ℝ)) (28757 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((1795441 / 500000 : ℝ) / 16) (125161 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_14 :
    (16263 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (7 / 100 : ℝ) (3 / 40 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (7 / 100 : ℝ) (3 / 40 : ℝ) (115027 / 100000 : ℝ) (14523 / 12500 : ℝ)
    (125427 / 100000 : ℝ) (2665283 / 100000000 : ℝ) (16263 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (7 / 100 : ℝ)) (115027 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (3 / 40 : ℝ)) (14523 / 12500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((906199 / 250000 : ℝ) / 16) (125427 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_15 :
    (8073 / 5000 : ℝ) ≤ hpThetaTraceEndpointLower (3 / 40 : ℝ) (2 / 25 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (3 / 40 : ℝ) (2 / 25 : ℝ) (116183 / 100000 : ℝ) (14669 / 12500 : ℝ)
    (3928 / 3125 : ℝ) (2575471 / 100000000 : ℝ) (8073 / 5000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (3 / 40 : ℝ)) (116183 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (2 / 25 : ℝ)) (14669 / 12500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((228693 / 62500 : ℝ) / 16) (3928 / 3125 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_16 :
    (16021 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (2 / 25 : ℝ) (17 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (2 / 25 : ℝ) (17 / 200 : ℝ) (117351 / 100000 : ℝ) (118531 / 100000 : ℝ)
    (125969 / 100000 : ℝ) (2487603 / 100000000 : ℝ) (16021 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (2 / 25 : ℝ)) (117351 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (17 / 200 : ℝ)) (118531 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((7387453 / 2000000 : ℝ) / 16) (125969 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_17 :
    (1589 / 1000 : ℝ) ≤ hpThetaTraceEndpointLower (17 / 200 : ℝ) (9 / 100 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (17 / 200 : ℝ) (9 / 100 : ℝ) (11853 / 10000 : ℝ) (59861 / 50000 : ℝ)
    (25249 / 20000 : ℝ) (1201 / 50000 : ℝ) (1589 / 1000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (17 / 200 : ℝ)) (11853 / 10000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (9 / 100 : ℝ)) (59861 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((3728743 / 1000000 : ℝ) / 16) (25249 / 20000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_18 :
    (15753 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (9 / 100 : ℝ) (19 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (9 / 100 : ℝ) (19 / 200 : ℝ) (119721 / 100000 : ℝ) (4837 / 4000 : ℝ)
    (31631 / 25000 : ℝ) (28983 / 1250000 : ℝ) (15753 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (9 / 100 : ℝ)) (119721 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (19 / 200 : ℝ)) (4837 / 4000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((301131 / 80000 : ℝ) / 16) (31631 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_19 :
    (1951 / 1250 : ℝ) ≤ hpThetaTraceEndpointLower (19 / 200 : ℝ) (1 / 10 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (19 / 200 : ℝ) (1 / 10 : ℝ) (30231 / 25000 : ℝ) (122141 / 100000 : ℝ)
    (15851 / 12500 : ℝ) (447387 / 20000000 : ℝ) (1951 / 1250 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (19 / 200 : ℝ)) (30231 / 25000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (1 / 10 : ℝ)) (122141 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((7599883 / 2000000 : ℝ) / 16) (15851 / 12500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_20 :
    (15459 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 10 : ℝ) (21 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (1 / 10 : ℝ) (21 / 200 : ℝ) (6107 / 5000 : ℝ) (15421 / 12500 : ℝ)
    (63547 / 50000 : ℝ) (107887 / 5000000 : ℝ) (15459 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (1 / 10 : ℝ)) (6107 / 5000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (21 / 200 : ℝ)) (15421 / 12500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((959023 / 250000 : ℝ) / 16) (63547 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_21 :
    (7651 / 5000 : ℝ) ≤ hpThetaTraceEndpointLower (21 / 200 : ℝ) (11 / 100 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (21 / 200 : ℝ) (11 / 100 : ℝ) (123367 / 100000 : ℝ) (3894 / 3125 : ℝ)
    (25477 / 20000 : ℝ) (208021 / 10000000 : ℝ) (7651 / 5000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (21 / 200 : ℝ)) (123367 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (11 / 100 : ℝ)) (3894 / 3125 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((968163 / 250000 : ℝ) / 16) (25477 / 20000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_22 :
    (7569 / 5000 : ℝ) ≤ hpThetaTraceEndpointLower (11 / 100 : ℝ) (23 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (11 / 100 : ℝ) (23 / 200 : ℝ) (124607 / 100000 : ℝ) (125861 / 100000 : ℝ)
    (798 / 625 : ℝ) (2004629 / 100000000 : ℝ) (7569 / 5000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (11 / 100 : ℝ)) (124607 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (23 / 200 : ℝ)) (125861 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((7819243 / 2000000 : ℝ) / 16) (798 / 625 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_23 :
    (14971 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (23 / 200 : ℝ) (3 / 25 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (23 / 200 : ℝ) (3 / 25 : ℝ) (6293 / 5000 : ℝ) (1017 / 800 : ℝ)
    (63989 / 50000 : ℝ) (1931233 / 100000000 : ℝ) (14971 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (23 / 200 : ℝ)) (6293 / 5000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (3 / 25 : ℝ)) (1017 / 800 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((63151 / 16000 : ℝ) / 16) (63989 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_24 :
    (14797 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (3 / 25 : ℝ) (1 / 8 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (3 / 25 : ℝ) (1 / 8 : ℝ) (31781 / 25000 : ℝ) (128403 / 100000 : ℝ)
    (3207 / 2500 : ℝ) (1859759 / 100000000 : ℝ) (14797 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (3 / 25 : ℝ)) (31781 / 25000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (1 / 8 : ℝ)) (128403 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((7969389 / 2000000 : ℝ) / 16) (3207 / 2500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_25 :
    (14617 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 8 : ℝ) (13 / 100 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (1 / 8 : ℝ) (13 / 100 : ℝ) (64201 / 50000 : ℝ) (64847 / 50000 : ℝ)
    (128587 / 100000 : ℝ) (71599 / 4000000 : ℝ) (14617 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (1 / 8 : ℝ)) (64201 / 50000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (13 / 100 : ℝ)) (64847 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((4022861 / 1000000 : ℝ) / 16) (128587 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_26 :
    (14433 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (13 / 100 : ℝ) (27 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (13 / 100 : ℝ) (27 / 200 : ℝ) (129693 / 100000 : ℝ) (130997 / 100000 : ℝ)
    (128897 / 100000 : ℝ) (430581 / 25000000 : ℝ) (14433 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (13 / 100 : ℝ)) (129693 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (27 / 200 : ℝ)) (130997 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((8122811 / 2000000 : ℝ) / 16) (128897 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_27 :
    (2849 / 2000 : ℝ) ≤ hpThetaTraceEndpointLower (27 / 200 : ℝ) (7 / 50 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (27 / 200 : ℝ) (7 / 50 : ℝ) (32749 / 25000 : ℝ) (132313 / 100000 : ℝ)
    (129211 / 100000 : ℝ) (1656563 / 100000000 : ℝ) (2849 / 2000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (27 / 200 : ℝ)) (32749 / 25000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (7 / 50 : ℝ)) (132313 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((8200719 / 2000000 : ℝ) / 16) (129211 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_28 :
    (281 / 200 : ℝ) ≤ hpThetaTraceEndpointLower (7 / 50 : ℝ) (29 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (7 / 50 : ℝ) (29 / 200 : ℝ) (16539 / 12500 : ℝ) (133643 / 100000 : ℝ)
    (12953 / 10000 : ℝ) (9953 / 625000 : ℝ) (281 / 200 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (7 / 50 : ℝ)) (16539 / 12500 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (29 / 200 : ℝ)) (133643 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((8279509 / 2000000 : ℝ) / 16) (12953 / 10000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_29 :
    (13853 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (29 / 200 : ℝ) (3 / 20 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (29 / 200 : ℝ) (3 / 20 : ℝ) (66821 / 50000 : ℝ) (67493 / 50000 : ℝ)
    (32463 / 25000 : ℝ) (1530459 / 100000000 : ℝ) (13853 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (29 / 200 : ℝ)) (66821 / 50000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (3 / 20 : ℝ)) (67493 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((4179559 / 1000000 : ℝ) / 16) (32463 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_30 :
    (13651 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (3 / 20 : ℝ) (31 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (3 / 20 : ℝ) (31 / 200 : ℝ) (26997 / 20000 : ℝ) (136343 / 100000 : ℝ)
    (130179 / 100000 : ℝ) (1470093 / 100000000 : ℝ) (13651 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (3 / 20 : ℝ)) (26997 / 20000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (31 / 200 : ℝ)) (136343 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((8439609 / 2000000 : ℝ) / 16) (130179 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_31 :
    (2689 / 2000 : ℝ) ≤ hpThetaTraceEndpointLower (31 / 200 : ℝ) (4 / 25 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (31 / 200 : ℝ) (4 / 25 : ℝ) (68171 / 50000 : ℝ) (137713 / 100000 : ℝ)
    (13051 / 10000 : ℝ) (35289 / 2500000 : ℝ) (2689 / 2000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (31 / 200 : ℝ)) (68171 / 50000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (4 / 25 : ℝ)) (137713 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((8520919 / 2000000 : ℝ) / 16) (13051 / 10000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_32 :
    (6617 / 5000 : ℝ) ≤ hpThetaTraceEndpointLower (4 / 25 : ℝ) (33 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (4 / 25 : ℝ) (33 / 200 : ℝ) (8607 / 6250 : ℝ) (139097 / 100000 : ℝ)
    (65423 / 50000 : ℝ) (1354667 / 100000000 : ℝ) (6617 / 5000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (4 / 25 : ℝ)) (8607 / 6250 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (33 / 200 : ℝ)) (139097 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((8603111 / 2000000 : ℝ) / 16) (65423 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_33 :
    (13021 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (33 / 200 : ℝ) (17 / 100 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (33 / 200 : ℝ) (17 / 100 : ℝ) (17387 / 12500 : ℝ) (28099 / 20000 : ℝ)
    (65593 / 50000 : ℝ) (1299571 / 100000000 : ℝ) (13021 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (33 / 200 : ℝ)) (17387 / 12500 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (17 / 100 : ℝ)) (28099 / 20000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((1737237 / 400000 : ℝ) / 16) (65593 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_34 :
    (3201 / 2500 : ℝ) ≤ hpThetaTraceEndpointLower (17 / 100 : ℝ) (7 / 40 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (17 / 100 : ℝ) (7 / 40 : ℝ) (70247 / 50000 : ℝ) (141907 / 100000 : ℝ)
    (131531 / 100000 : ℝ) (1246091 / 100000000 : ℝ) (3201 / 2500 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (17 / 100 : ℝ)) (70247 / 50000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (7 / 40 : ℝ)) (141907 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((8770141 / 2000000 : ℝ) / 16) (131531 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_35 :
    (1573 / 1250 : ℝ) ≤ hpThetaTraceEndpointLower (7 / 40 : ℝ) (9 / 50 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (7 / 40 : ℝ) (9 / 50 : ℝ) (70953 / 50000 : ℝ) (143333 / 100000 : ℝ)
    (3297 / 2500 : ℝ) (298591 / 25000000 : ℝ) (1573 / 1250 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (7 / 40 : ℝ)) (70953 / 50000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (9 / 50 : ℝ)) (143333 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((8854979 / 2000000 : ℝ) / 16) (3297 / 2500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_36 :
    (12361 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (9 / 50 : ℝ) (37 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (9 / 50 : ℝ) (37 / 200 : ℝ) (35833 / 25000 : ℝ) (72387 / 50000 : ℝ)
    (66117 / 50000 : ℝ) (57211 / 5000000 : ℝ) (12361 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (9 / 50 : ℝ)) (35833 / 25000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (37 / 200 : ℝ)) (72387 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((4470381 / 1000000 : ℝ) / 16) (66117 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_37 :
    (1517 / 1250 : ℝ) ≤ hpThetaTraceEndpointLower (37 / 200 : ℝ) (19 / 100 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (37 / 200 : ℝ) (19 / 100 : ℝ) (144773 / 100000 : ℝ) (146229 / 100000 : ℝ)
    (132593 / 100000 : ℝ) (547823 / 50000000 : ℝ) (1517 / 1250 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (37 / 200 : ℝ)) (144773 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (19 / 100 : ℝ)) (146229 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((9027427 / 2000000 : ℝ) / 16) (132593 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_38 :
    (11909 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (19 / 100 : ℝ) (39 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (19 / 100 : ℝ) (39 / 200 : ℝ) (36557 / 25000 : ℝ) (147699 / 100000 : ℝ)
    (33239 / 25000 : ℝ) (65547 / 6250000 : ℝ) (11909 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (19 / 100 : ℝ)) (36557 / 25000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (39 / 200 : ℝ)) (147699 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((9115037 / 2000000 : ℝ) / 16) (33239 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_39 :
    (146 / 125 : ℝ) ≤ hpThetaTraceEndpointLower (39 / 200 : ℝ) (1 / 5 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (39 / 200 : ℝ) (1 / 5 : ℝ) (73849 / 50000 : ℝ) (149183 / 100000 : ℝ)
    (33331 / 25000 : ℝ) (501691 / 50000000 : ℝ) (146 / 125 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (39 / 200 : ℝ)) (73849 / 50000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (1 / 5 : ℝ)) (149183 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((9203529 / 2000000 : ℝ) / 16) (33331 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_40 :
    (11449 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 5 : ℝ) (41 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (1 / 5 : ℝ) (41 / 200 : ℝ) (74591 / 50000 : ℝ) (75341 / 50000 : ℝ)
    (133697 / 100000 : ℝ) (479759 / 50000000 : ℝ) (11449 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (1 / 5 : ℝ)) (74591 / 50000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (41 / 200 : ℝ)) (75341 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((4646483 / 1000000 : ℝ) / 16) (133697 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_41 :
    (701 / 625 : ℝ) ≤ hpThetaTraceEndpointLower (41 / 200 : ℝ) (21 / 100 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (41 / 200 : ℝ) (21 / 100 : ℝ) (150681 / 100000 : ℝ) (152197 / 100000 : ℝ)
    (33519 / 25000 : ℝ) (917029 / 100000000 : ℝ) (701 / 625 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (41 / 200 : ℝ)) (150681 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (21 / 100 : ℝ)) (152197 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((9383411 / 2000000 : ℝ) / 16) (33519 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_42 :
    (5491 / 5000 : ℝ) ≤ hpThetaTraceEndpointLower (21 / 100 : ℝ) (43 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (21 / 100 : ℝ) (43 / 200 : ℝ) (38049 / 25000 : ℝ) (76863 / 50000 : ℝ)
    (134459 / 100000 : ℝ) (219029 / 25000000 : ℝ) (5491 / 5000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (21 / 100 : ℝ)) (38049 / 25000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (43 / 200 : ℝ)) (76863 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((4737369 / 1000000 : ℝ) / 16) (134459 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_43 :
    (10747 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (43 / 200 : ℝ) (11 / 50 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (43 / 200 : ℝ) (11 / 50 : ℝ) (6149 / 4000 : ℝ) (155271 / 100000 : ℝ)
    (4214 / 3125 : ℝ) (418271 / 50000000 : ℝ) (10747 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (43 / 200 : ℝ)) (6149 / 4000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (11 / 50 : ℝ)) (155271 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((9567073 / 2000000 : ℝ) / 16) (4214 / 3125 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_44 :
    (657 / 625 : ℝ) ≤ hpThetaTraceEndpointLower (11 / 50 : ℝ) (9 / 40 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (11 / 50 : ℝ) (9 / 40 : ℝ) (15527 / 10000 : ℝ) (4901 / 3125 : ℝ)
    (135241 / 100000 : ℝ) (798483 / 100000000 : ℝ) (657 / 625 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (11 / 50 : ℝ)) (15527 / 10000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (9 / 40 : ℝ)) (4901 / 3125 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((75472 / 15625 : ℝ) / 16) (135241 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_45 :
    (411 / 400 : ℝ) ≤ hpThetaTraceEndpointLower (9 / 40 : ℝ) (23 / 100 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (9 / 40 : ℝ) (23 / 100 : ℝ) (156831 / 100000 : ℝ) (19801 / 12500 : ℝ)
    (135641 / 100000 : ℝ) (76163 / 10000000 : ℝ) (411 / 400 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (9 / 40 : ℝ)) (156831 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (23 / 100 : ℝ)) (19801 / 12500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((609669 / 125000 : ℝ) / 16) (135641 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_46 :
    (10039 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (23 / 100 : ℝ) (47 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (23 / 100 : ℝ) (47 / 200 : ℝ) (158407 / 100000 : ℝ) (8 / 5 : ℝ)
    (27209 / 20000 : ℝ) (726237 / 100000000 : ℝ) (10039 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (23 / 100 : ℝ)) (158407 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (47 / 200 : ℝ)) (8 / 5 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((197 / 40 : ℝ) / 16) (27209 / 20000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_47 :
    (4901 / 5000 : ℝ) ≤ hpThetaTraceEndpointLower (47 / 200 : ℝ) (6 / 25 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (47 / 200 : ℝ) (6 / 25 : ℝ) (159999 / 100000 : ℝ) (20201 / 12500 : ℝ)
    (27291 / 20000 : ℝ) (692099 / 100000000 : ℝ) (4901 / 5000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (47 / 200 : ℝ)) (159999 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (6 / 25 : ℝ)) (20201 / 12500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((155411 / 31250 : ℝ) / 16) (27291 / 20000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_48 :
    (1913 / 2000 : ℝ) ≤ hpThetaTraceEndpointLower (6 / 25 : ℝ) (49 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (6 / 25 : ℝ) (49 / 200 : ℝ) (161607 / 100000 : ℝ) (5101 / 3125 : ℝ)
    (136871 / 100000 : ℝ) (659199 / 100000000 : ℝ) (1913 / 2000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (6 / 25 : ℝ)) (161607 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (49 / 200 : ℝ)) (5101 / 3125 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((313863 / 62500 : ℝ) / 16) (136871 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_49 :
    (9329 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (49 / 200 : ℝ) (1 / 4 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (49 / 200 : ℝ) (1 / 4 : ℝ) (163231 / 100000 : ℝ) (164873 / 100000 : ℝ)
    (34323 / 25000 : ℝ) (62759 / 10000000 : ℝ) (9329 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (49 / 200 : ℝ)) (163231 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (1 / 4 : ℝ)) (164873 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((10141999 / 2000000 : ℝ) / 16) (34323 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_50 :
    (4547 / 5000 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 4 : ℝ) (51 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (1 / 4 : ℝ) (51 / 200 : ℝ) (20609 / 12500 : ℝ) (16653 / 10000 : ℝ)
    (137719 / 100000 : ℝ) (59717 / 10000000 : ℝ) (4547 / 5000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (1 / 4 : ℝ)) (20609 / 12500 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (51 / 200 : ℝ)) (16653 / 10000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((1024139 / 200000 : ℝ) / 16) (137719 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_51 :
    (8859 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (51 / 200 : ℝ) (13 / 50 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (51 / 200 : ℝ) (13 / 50 : ℝ) (166529 / 100000 : ℝ) (168203 / 100000 : ℝ)
    (17269 / 12500 : ℝ) (567917 / 100000000 : ℝ) (8859 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (51 / 200 : ℝ)) (166529 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (13 / 50 : ℝ)) (168203 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((10341789 / 2000000 : ℝ) / 16) (17269 / 12500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_52 :
    (69 / 80 : ℝ) ≤ hpThetaTraceEndpointLower (13 / 50 : ℝ) (53 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (13 / 50 : ℝ) (53 / 200 : ℝ) (84101 / 50000 : ℝ) (84947 / 50000 : ℝ)
    (138591 / 100000 : ℝ) (16869 / 3125000 : ℝ) (69 / 80 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (13 / 50 : ℝ)) (84101 / 50000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (53 / 200 : ℝ)) (84947 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((5221661 / 1000000 : ℝ) / 16) (138591 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_53 :
    (1049 / 1250 : ℝ) ≤ hpThetaTraceEndpointLower (53 / 200 : ℝ) (27 / 100 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (53 / 200 : ℝ) (27 / 100 : ℝ) (169893 / 100000 : ℝ) (171601 / 100000 : ℝ)
    (34759 / 25000 : ℝ) (256409 / 50000000 : ℝ) (1049 / 1250 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (53 / 200 : ℝ)) (169893 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (27 / 100 : ℝ)) (171601 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((10545863 / 2000000 : ℝ) / 16) (34759 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_54 :
    (8161 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (27 / 100 : ℝ) (11 / 40 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (27 / 100 : ℝ) (11 / 40 : ℝ) (429 / 250 : ℝ) (86663 / 50000 : ℝ)
    (139487 / 100000 : ℝ) (243461 / 50000000 : ℝ) (8161 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (27 / 100 : ℝ)) (429 / 250 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (11 / 40 : ℝ)) (86663 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((5324769 / 1000000 : ℝ) / 16) (139487 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_55 :
    (7931 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (11 / 40 : ℝ) (7 / 25 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (11 / 40 : ℝ) (7 / 25 : ℝ) (6933 / 4000 : ℝ) (43767 / 25000 : ℝ)
    (17493 / 12500 : ℝ) (92419 / 20000000 : ℝ) (7931 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (11 / 40 : ℝ)) (6933 / 4000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (7 / 25 : ℝ)) (43767 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((2688571 / 500000 : ℝ) / 16) (17493 / 12500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_56 :
    (7703 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (7 / 25 : ℝ) (57 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (7 / 25 : ℝ) (57 / 200 : ℝ) (175067 / 100000 : ℝ) (176827 / 100000 : ℝ)
    (17551 / 12500 : ℝ) (219129 / 50000000 : ℝ) (7703 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (7 / 25 : ℝ)) (175067 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (57 / 200 : ℝ)) (176827 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((10860101 / 2000000 : ℝ) / 16) (17551 / 12500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_57 :
    (7477 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (57 / 200 : ℝ) (29 / 100 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (57 / 200 : ℝ) (29 / 100 : ℝ) (88413 / 50000 : ℝ) (44651 / 25000 : ℝ)
    (70439 / 50000 : ℝ) (5193 / 1250000 : ℝ) (7477 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (57 / 200 : ℝ)) (88413 / 50000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (29 / 100 : ℝ)) (44651 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((2741763 / 500000 : ℝ) / 16) (70439 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_58 :
    (7253 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (29 / 100 : ℝ) (59 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (29 / 100 : ℝ) (59 / 200 : ℝ) (178603 / 100000 : ℝ) (180399 / 100000 : ℝ)
    (28271 / 20000 : ℝ) (393569 / 100000000 : ℝ) (7253 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (29 / 100 : ℝ)) (178603 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (59 / 200 : ℝ)) (180399 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((11075137 / 2000000 : ℝ) / 16) (28271 / 20000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_59 :
    (879 / 1250 : ℝ) ≤ hpThetaTraceEndpointLower (59 / 200 : ℝ) (3 / 10 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (59 / 200 : ℝ) (3 / 10 : ℝ) (90199 / 50000 : ℝ) (45553 / 25000 : ℝ)
    (70919 / 50000 : ℝ) (46583 / 12500000 : ℝ) (879 / 1250 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (59 / 200 : ℝ)) (90199 / 50000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (3 / 10 : ℝ)) (45553 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((2796089 / 500000 : ℝ) / 16) (70919 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_60 :
    (3407 / 5000 : ℝ) ≤ hpThetaTraceEndpointLower (3 / 10 : ℝ) (61 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (3 / 10 : ℝ) (61 / 200 : ℝ) (182211 / 100000 : ℝ) (46011 / 25000 : ℝ)
    (17791 / 12500 : ℝ) (176329 / 50000000 : ℝ) (3407 / 5000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (3 / 10 : ℝ)) (182211 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (61 / 200 : ℝ)) (46011 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((2823693 / 500000 : ℝ) / 16) (17791 / 12500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_61 :
    (6597 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (61 / 200 : ℝ) (31 / 100 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (61 / 200 : ℝ) (31 / 100 : ℝ) (184043 / 100000 : ℝ) (185893 / 100000 : ℝ)
    (5713 / 4000 : ℝ) (333527 / 100000000 : ℝ) (6597 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (61 / 200 : ℝ)) (184043 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (31 / 100 : ℝ)) (185893 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((11406259 / 2000000 : ℝ) / 16) (5713 / 4000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_62 :
    (399 / 625 : ℝ) ≤ hpThetaTraceEndpointLower (31 / 100 : ℝ) (63 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (31 / 100 : ℝ) (63 / 200 : ℝ) (46473 / 25000 : ℝ) (93881 / 50000 : ℝ)
    (143329 / 100000 : ℝ) (315249 / 100000000 : ℝ) (399 / 625 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (31 / 100 : ℝ)) (46473 / 25000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (63 / 200 : ℝ)) (93881 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((5759503 / 1000000 : ℝ) / 16) (143329 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_63 :
    (3087 / 5000 : ℝ) ≤ hpThetaTraceEndpointLower (63 / 200 : ℝ) (8 / 25 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (63 / 200 : ℝ) (8 / 25 : ℝ) (187761 / 100000 : ℝ) (189649 / 100000 : ℝ)
    (899 / 625 : ℝ) (1489 / 500000 : ℝ) (3087 / 5000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (63 / 200 : ℝ)) (187761 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (8 / 25 : ℝ)) (189649 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((11632887 / 2000000 : ℝ) / 16) (899 / 625 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_64 :
    (5967 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (8 / 25 : ℝ) (13 / 40 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (8 / 25 : ℝ) (13 / 40 : ℝ) (11853 / 6250 : ℝ) (38311 / 20000 : ℝ)
    (72179 / 50000 : ℝ) (56231 / 20000000 : ℝ) (5967 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (8 / 25 : ℝ)) (11853 / 6250 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (13 / 40 : ℝ)) (38311 / 20000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((2349593 / 400000 : ℝ) / 16) (72179 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_65 :
    (2881 / 5000 : ℝ) ≤ hpThetaTraceEndpointLower (13 / 40 : ℝ) (33 / 100 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (13 / 40 : ℝ) (33 / 100 : ℝ) (95777 / 50000 : ℝ) (4837 / 2500 : ℝ)
    (36221 / 25000 : ℝ) (13263 / 5000000 : ℝ) (2881 / 5000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (13 / 40 : ℝ)) (95777 / 50000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (33 / 100 : ℝ)) (4837 / 2500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((148303 / 25000 : ℝ) / 16) (36221 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_66 :
    (5561 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (33 / 100 : ℝ) (67 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (33 / 100 : ℝ) (67 / 200 : ℝ) (193479 / 100000 : ℝ) (6107 / 3125 : ℝ)
    (145417 / 100000 : ℝ) (2001 / 800000 : ℝ) (5561 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (33 / 100 : ℝ)) (193479 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (67 / 200 : ℝ)) (6107 / 3125 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((748857 / 125000 : ℝ) / 16) (145417 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_67 :
    (1341 / 2500 : ℝ) ≤ hpThetaTraceEndpointLower (67 / 200 : ℝ) (17 / 50 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (67 / 200 : ℝ) (17 / 50 : ℝ) (195423 / 100000 : ℝ) (49347 / 25000 : ℝ)
    (145957 / 100000 : ℝ) (117861 / 50000000 : ℝ) (1341 / 2500 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (67 / 200 : ℝ)) (195423 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (17 / 50 : ℝ)) (49347 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((3025111 / 500000 : ℝ) / 16) (145957 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_68 :
    (5171 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (17 / 50 : ℝ) (69 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (17 / 50 : ℝ) (69 / 200 : ℝ) (197387 / 100000 : ℝ) (49843 / 25000 : ℝ)
    (29301 / 20000 : ℝ) (55501 / 25000000 : ℝ) (5171 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (17 / 50 : ℝ)) (197387 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (69 / 200 : ℝ)) (49843 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((3055109 / 500000 : ℝ) / 16) (29301 / 20000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_69 :
    (249 / 500 : ℝ) ≤ hpThetaTraceEndpointLower (69 / 200 : ℝ) (7 / 20 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (69 / 200 : ℝ) (7 / 20 : ℝ) (199371 / 100000 : ℝ) (6293 / 3125 : ℝ)
    (73531 / 50000 : ℝ) (104463 / 50000000 : ℝ) (249 / 500 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (69 / 200 : ℝ)) (199371 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (7 / 20 : ℝ)) (6293 / 3125 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((1542711 / 250000 : ℝ) / 16) (73531 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_70 :
    (2397 / 5000 : ℝ) ≤ hpThetaTraceEndpointLower (7 / 20 : ℝ) (71 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (7 / 20 : ℝ) (71 / 200 : ℝ) (1611 / 800 : ℝ) (1017 / 500 : ℝ)
    (73813 / 50000 : ℝ) (98257 / 50000000 : ℝ) (2397 / 5000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (7 / 20 : ℝ)) (1611 / 800 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (71 / 200 : ℝ)) (1017 / 500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((62321 / 10000 : ℝ) / 16) (73813 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_71 :
    (1153 / 2500 : ℝ) ≤ hpThetaTraceEndpointLower (71 / 200 : ℝ) (9 / 25 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (71 / 200 : ℝ) (9 / 25 : ℝ) (203399 / 100000 : ℝ) (51361 / 25000 : ℝ)
    (74099 / 50000 : ℝ) (184723 / 100000000 : ℝ) (1153 / 2500 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (71 / 200 : ℝ)) (203399 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (9 / 25 : ℝ)) (51361 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((3146993 / 500000 : ℝ) / 16) (74099 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_72 :
    (4433 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (9 / 25 : ℝ) (73 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (9 / 25 : ℝ) (73 / 200 : ℝ) (205443 / 100000 : ℝ) (207509 / 100000 : ℝ)
    (74389 / 50000 : ℝ) (43383 / 25000000 : ℝ) (4433 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (9 / 25 : ℝ)) (205443 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (73 / 200 : ℝ)) (207509 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((12713067 / 2000000 : ℝ) / 16) (74389 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_73 :
    (4259 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (73 / 200 : ℝ) (37 / 100 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (73 / 200 : ℝ) (37 / 100 : ℝ) (51877 / 25000 : ℝ) (104797 / 50000 : ℝ)
    (149367 / 100000 : ℝ) (162901 / 100000000 : ℝ) (4259 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (73 / 200 : ℝ)) (51877 / 25000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (37 / 100 : ℝ)) (104797 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((6419711 / 1000000 : ℝ) / 16) (149367 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_74 :
    (511 / 1250 : ℝ) ≤ hpThetaTraceEndpointLower (37 / 100 : ℝ) (3 / 8 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (37 / 100 : ℝ) (3 / 8 : ℝ) (209593 / 100000 : ℝ) (211701 / 100000 : ℝ)
    (37491 / 25000 : ℝ) (152829 / 100000000 : ℝ) (511 / 1250 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (37 / 100 : ℝ)) (209593 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (3 / 8 : ℝ)) (211701 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((12967163 / 2000000 : ℝ) / 16) (37491 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_75 :
    (1961 / 5000 : ℝ) ≤ hpThetaTraceEndpointLower (3 / 8 : ℝ) (19 / 50 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (3 / 8 : ℝ) (19 / 50 : ℝ) (2117 / 1000 : ℝ) (53457 / 25000 : ℝ)
    (15057 / 10000 : ℝ) (143279 / 100000000 : ℝ) (1961 / 5000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (3 / 8 : ℝ)) (2117 / 1000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (19 / 50 : ℝ)) (53457 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((3274041 / 500000 : ℝ) / 16) (15057 / 10000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_76 :
    (3759 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (19 / 50 : ℝ) (77 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (19 / 50 : ℝ) (77 / 200 : ℝ) (213827 / 100000 : ℝ) (215977 / 100000 : ℝ)
    (30237 / 20000 : ℝ) (134233 / 100000000 : ℝ) (3759 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (19 / 50 : ℝ)) (213827 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (77 / 200 : ℝ)) (215977 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((13226551 / 2000000 : ℝ) / 16) (30237 / 20000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_77 :
    (3601 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (77 / 200 : ℝ) (39 / 100 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (77 / 200 : ℝ) (39 / 100 : ℝ) (26997 / 12500 : ℝ) (54537 / 25000 : ℝ)
    (151809 / 100000 : ℝ) (15709 / 12500000 : ℝ) (3601 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (77 / 200 : ℝ)) (26997 / 12500 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (39 / 100 : ℝ)) (54537 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((3339581 / 500000 : ℝ) / 16) (151809 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_78 :
    (3447 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (39 / 100 : ℝ) (79 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (39 / 100 : ℝ) (79 / 200 : ℝ) (218147 / 100000 : ℝ) (11017 / 5000 : ℝ)
    (152441 / 100000 : ℝ) (11759 / 10000000 : ℝ) (3447 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (39 / 100 : ℝ)) (218147 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (79 / 200 : ℝ)) (11017 / 5000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((674571 / 100000 : ℝ) / 16) (152441 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_79 :
    (3297 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (79 / 200 : ℝ) (2 / 5 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (79 / 200 : ℝ) (2 / 5 : ℝ) (220339 / 100000 : ℝ) (44511 / 20000 : ℝ)
    (38271 / 25000 : ℝ) (109931 / 100000000 : ℝ) (3297 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (79 / 200 : ℝ)) (220339 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (2 / 5 : ℝ)) (44511 / 20000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((2725193 / 400000 : ℝ) / 16) (38271 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_80 :
    (3151 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (2 / 5 : ℝ) (81 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (2 / 5 : ℝ) (81 / 200 : ℝ) (111277 / 50000 : ℝ) (224791 / 100000 : ℝ)
    (30747 / 20000 : ℝ) (20543 / 20000000 : ℝ) (3151 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (2 / 5 : ℝ)) (111277 / 50000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (81 / 200 : ℝ)) (224791 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((13761833 / 2000000 : ℝ) / 16) (30747 / 20000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_81 :
    (301 / 1000 : ℝ) ≤ hpThetaTraceEndpointLower (81 / 200 : ℝ) (41 / 100 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (81 / 200 : ℝ) (41 / 100 : ℝ) (22479 / 10000 : ℝ) (4541 / 2000 : ℝ)
    (38599 / 25000 : ℝ) (95901 / 100000000 : ℝ) (301 / 1000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (81 / 200 : ℝ)) (22479 / 10000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (41 / 100 : ℝ)) (4541 / 2000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((277983 / 40000 : ℝ) / 16) (38599 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_82 :
    (359 / 1250 : ℝ) ≤ hpThetaTraceEndpointLower (41 / 100 : ℝ) (83 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (41 / 100 : ℝ) (83 / 200 : ℝ) (227049 / 100000 : ℝ) (57333 / 25000 : ℝ)
    (155067 / 100000 : ℝ) (699 / 781250 : ℝ) (359 / 1250 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (41 / 100 : ℝ)) (227049 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (83 / 200 : ℝ)) (57333 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((3509479 / 500000 : ℝ) / 16) (155067 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_83 :
    (2739 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (83 / 200 : ℝ) (21 / 50 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (83 / 200 : ℝ) (21 / 50 : ℝ) (229331 / 100000 : ℝ) (231637 / 100000 : ℝ)
    (38937 / 25000 : ℝ) (41707 / 50000000 : ℝ) (2739 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (83 / 200 : ℝ)) (229331 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (21 / 50 : ℝ)) (231637 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((14178131 / 2000000 : ℝ) / 16) (38937 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_84 :
    (261 / 1000 : ℝ) ≤ hpThetaTraceEndpointLower (21 / 50 : ℝ) (17 / 40 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (21 / 50 : ℝ) (17 / 40 : ℝ) (57909 / 25000 : ℝ) (46793 / 20000 : ℝ)
    (156439 / 100000 : ℝ) (7771 / 10000000 : ℝ) (261 / 1000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (21 / 50 : ℝ)) (57909 / 25000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (17 / 40 : ℝ)) (46793 / 20000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((2863959 / 400000 : ℝ) / 16) (156439 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_85 :
    (497 / 2000 : ℝ) ≤ hpThetaTraceEndpointLower (17 / 40 : ℝ) (43 / 100 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (17 / 40 : ℝ) (43 / 100 : ℝ) (58491 / 25000 : ℝ) (236317 / 100000 : ℝ)
    (157141 / 100000 : ℝ) (36169 / 50000000 : ℝ) (497 / 2000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (17 / 40 : ℝ)) (58491 / 25000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (43 / 100 : ℝ)) (236317 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((14462971 / 2000000 : ℝ) / 16) (157141 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_86 :
    (473 / 2000 : ℝ) ≤ hpThetaTraceEndpointLower (43 / 100 : ℝ) (87 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (43 / 100 : ℝ) (87 / 200 : ℝ) (59079 / 25000 : ℝ) (59673 / 25000 : ℝ)
    (39463 / 25000 : ℝ) (67297 / 100000000 : ℝ) (473 / 2000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (43 / 100 : ℝ)) (59079 / 25000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (87 / 200 : ℝ)) (59673 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((3651899 / 500000 : ℝ) / 16) (39463 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_87 :
    (281 / 1250 : ℝ) ≤ hpThetaTraceEndpointLower (87 / 200 : ℝ) (11 / 25 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (87 / 200 : ℝ) (11 / 25 : ℝ) (238691 / 100000 : ℝ) (24109 / 10000 : ℝ)
    (6343 / 4000 : ℝ) (7819 / 12500000 : ℝ) (281 / 1250 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (87 / 200 : ℝ)) (238691 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (11 / 25 : ℝ)) (24109 / 10000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((1475367 / 200000 : ℝ) / 16) (6343 / 4000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_88 :
    (427 / 2000 : ℝ) ≤ hpThetaTraceEndpointLower (11 / 25 : ℝ) (89 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (11 / 25 : ℝ) (89 / 200 : ℝ) (241089 / 100000 : ℝ) (243513 / 100000 : ℝ)
    (39827 / 25000 : ℝ) (58103 / 100000000 : ℝ) (427 / 2000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (11 / 25 : ℝ)) (241089 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (89 / 200 : ℝ)) (243513 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((14901319 / 2000000 : ℝ) / 16) (39827 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_89 :
    (2027 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (89 / 200 : ℝ) (9 / 20 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (89 / 200 : ℝ) (9 / 20 : ℝ) (30439 / 12500 : ℝ) (245961 / 100000 : ℝ)
    (160053 / 100000 : ℝ) (53923 / 100000000 : ℝ) (2027 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (89 / 200 : ℝ)) (30439 / 12500 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (9 / 20 : ℝ)) (245961 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((15050543 / 2000000 : ℝ) / 16) (160053 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_90 :
    (961 / 5000 : ℝ) ≤ hpThetaTraceEndpointLower (9 / 20 : ℝ) (91 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (9 / 20 : ℝ) (91 / 200 : ℝ) (6149 / 2500 : ℝ) (248433 / 100000 : ℝ)
    (20101 / 12500 : ℝ) (12503 / 25000000 : ℝ) (961 / 5000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (9 / 20 : ℝ)) (6149 / 2500 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (91 / 200 : ℝ)) (248433 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((15201279 / 2000000 : ℝ) / 16) (20101 / 12500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_91 :
    (911 / 5000 : ℝ) ≤ hpThetaTraceEndpointLower (91 / 200 : ℝ) (23 / 50 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (91 / 200 : ℝ) (23 / 50 : ℝ) (15527 / 6250 : ℝ) (25093 / 10000 : ℝ)
    (20197 / 12500 : ℝ) (46341 / 100000000 : ℝ) (911 / 5000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (91 / 200 : ℝ)) (15527 / 6250 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (23 / 50 : ℝ)) (25093 / 10000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((1535359 / 200000 : ℝ) / 16) (20197 / 12500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_92 :
    (69 / 400 : ℝ) ≤ hpThetaTraceEndpointLower (23 / 50 : ℝ) (93 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (23 / 50 : ℝ) (93 / 200 : ℝ) (250929 / 100000 : ℝ) (253451 / 100000 : ℝ)
    (81177 / 50000 : ℝ) (42913 / 100000000 : ℝ) (69 / 400 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (23 / 50 : ℝ)) (250929 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (93 / 200 : ℝ)) (253451 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((15507413 / 2000000 : ℝ) / 16) (81177 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_93 :
    (102 / 625 : ℝ) ≤ hpThetaTraceEndpointLower (93 / 200 : ℝ) (47 / 100 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (93 / 200 : ℝ) (47 / 100 : ℝ) (5069 / 2000 : ℝ) (255999 / 100000 : ℝ)
    (32629 / 20000 : ℝ) (19851 / 50000000 : ℝ) (102 / 625 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (93 / 200 : ℝ)) (5069 / 2000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (47 / 100 : ℝ)) (255999 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((15662937 / 2000000 : ℝ) / 16) (32629 / 20000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_94 :
    (1543 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (47 / 100 : ℝ) (19 / 40 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (47 / 100 : ℝ) (19 / 40 : ℝ) (127999 / 50000 : ℝ) (258571 / 100000 : ℝ)
    (40987 / 25000 : ℝ) (36703 / 100000000 : ℝ) (1543 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (47 / 100 : ℝ)) (127999 / 50000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (19 / 40 : ℝ)) (258571 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((15819973 / 2000000 : ℝ) / 16) (40987 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_95 :
    (1457 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (19 / 40 : ℝ) (12 / 25 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (19 / 40 : ℝ) (12 / 25 : ℝ) (25857 / 10000 : ℝ) (26117 / 10000 : ℝ)
    (164763 / 100000 : ℝ) (33903 / 100000000 : ℝ) (1457 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (19 / 40 : ℝ)) (25857 / 10000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (12 / 25 : ℝ)) (26117 / 10000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((1597871 / 200000 : ℝ) / 16) (164763 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_96 :
    (11 / 80 : ℝ) ≤ hpThetaTraceEndpointLower (12 / 25 : ℝ) (97 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (12 / 25 : ℝ) (97 / 200 : ℝ) (261169 / 100000 : ℝ) (52759 / 20000 : ℝ)
    (165591 / 100000 : ℝ) (3129 / 10000000 : ℝ) (11 / 80 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (12 / 25 : ℝ)) (261169 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (97 / 200 : ℝ)) (52759 / 20000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((3227817 / 400000 : ℝ) / 16) (165591 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_97 :
    (1297 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (97 / 200 : ℝ) (49 / 100 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (97 / 200 : ℝ) (49 / 100 : ℝ) (131897 / 50000 : ℝ) (133223 / 50000 : ℝ)
    (166431 / 100000 : ℝ) (28857 / 100000000 : ℝ) (1297 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (97 / 200 : ℝ)) (131897 / 50000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (49 / 100 : ℝ)) (133223 / 50000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((8150549 / 1000000 : ℝ) / 16) (166431 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_98 :
    (1221 / 10000 : ℝ) ≤ hpThetaTraceEndpointLower (49 / 100 : ℝ) (99 / 200 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (49 / 100 : ℝ) (99 / 200 : ℝ) (53289 / 20000 : ℝ) (67281 / 25000 : ℝ)
    (33457 / 20000 : ℝ) (6647 / 25000000 : ℝ) (1221 / 10000 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (49 / 100 : ℝ)) (53289 / 20000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (99 / 200 : ℝ)) (67281 / 25000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((4116203 / 500000 : ℝ) / 16) (33457 / 20000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

theorem hpThetaTrace_energy_endpoint_99 :
    (23 / 200 : ℝ) ≤ hpThetaTraceEndpointLower (99 / 200 : ℝ) (1 / 2 : ℝ) := by
  apply hpThetaTrace_rational_endpoint_certificate
    (99 / 200 : ℝ) (1 / 2 : ℝ) (269123 / 100000 : ℝ) (271829 / 100000 : ℝ)
    (21019 / 12500 : ℝ) (24477 / 100000000 : ℝ) (23 / 200 : ℝ)
  · norm_num
  · exact hpThetaTrace_exp_lower_of_taylor
      (2 * (99 / 200 : ℝ)) (269123 / 100000 : ℝ) 12 (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · exact hpThetaTrace_exp_upper_of_taylor
      (2 * (1 / 2 : ℝ)) (271829 / 100000 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
  · norm_num
  · norm_num
  · have h := hpThetaTrace_exp_upper_of_taylor
      ((16630227 / 2000000 : ℝ) / 16) (21019 / 12500 : ℝ) 12
      (by norm_num) (by norm_num) (by norm_num) (by norm_num [hpThetaTraceExpTaylorSum, hpThetaTraceExpTaylorUpper, Finset.sum_range_succ, Nat.factorial])
    norm_num at h ⊢
    exact h
  · norm_num
  · norm_num
  · norm_num

noncomputable def hpThetaTraceCertificateLeft (i : ℕ) : ℝ :=
  (i : ℝ) / 200

noncomputable def hpThetaTraceCertificateRight (i : ℕ) : ℝ :=
  ((i : ℝ) + 1) / 200

noncomputable def hpThetaTraceCertificateLower (i : ℕ) : ℝ :=
  match i with
  | 0 => (8551 / 5000 : ℝ)
  | 1 => (8547 / 5000 : ℝ)
  | 2 => (8539 / 5000 : ℝ)
  | 3 => (8527 / 5000 : ℝ)
  | 4 => (17023 / 10000 : ℝ)
  | 5 => (8491 / 5000 : ℝ)
  | 6 => (16933 / 10000 : ℝ)
  | 7 => (8439 / 5000 : ℝ)
  | 8 => (16813 / 10000 : ℝ)
  | 9 => (16739 / 10000 : ℝ)
  | 10 => (833 / 500 : ℝ)
  | 11 => (16573 / 10000 : ℝ)
  | 12 => (16477 / 10000 : ℝ)
  | 13 => (8187 / 5000 : ℝ)
  | 14 => (16263 / 10000 : ℝ)
  | 15 => (8073 / 5000 : ℝ)
  | 16 => (16021 / 10000 : ℝ)
  | 17 => (1589 / 1000 : ℝ)
  | 18 => (15753 / 10000 : ℝ)
  | 19 => (1951 / 1250 : ℝ)
  | 20 => (15459 / 10000 : ℝ)
  | 21 => (7651 / 5000 : ℝ)
  | 22 => (7569 / 5000 : ℝ)
  | 23 => (14971 / 10000 : ℝ)
  | 24 => (14797 / 10000 : ℝ)
  | 25 => (14617 / 10000 : ℝ)
  | 26 => (14433 / 10000 : ℝ)
  | 27 => (2849 / 2000 : ℝ)
  | 28 => (281 / 200 : ℝ)
  | 29 => (13853 / 10000 : ℝ)
  | 30 => (13651 / 10000 : ℝ)
  | 31 => (2689 / 2000 : ℝ)
  | 32 => (6617 / 5000 : ℝ)
  | 33 => (13021 / 10000 : ℝ)
  | 34 => (3201 / 2500 : ℝ)
  | 35 => (1573 / 1250 : ℝ)
  | 36 => (12361 / 10000 : ℝ)
  | 37 => (1517 / 1250 : ℝ)
  | 38 => (11909 / 10000 : ℝ)
  | 39 => (146 / 125 : ℝ)
  | 40 => (11449 / 10000 : ℝ)
  | 41 => (701 / 625 : ℝ)
  | 42 => (5491 / 5000 : ℝ)
  | 43 => (10747 / 10000 : ℝ)
  | 44 => (657 / 625 : ℝ)
  | 45 => (411 / 400 : ℝ)
  | 46 => (10039 / 10000 : ℝ)
  | 47 => (4901 / 5000 : ℝ)
  | 48 => (1913 / 2000 : ℝ)
  | 49 => (9329 / 10000 : ℝ)
  | 50 => (4547 / 5000 : ℝ)
  | 51 => (8859 / 10000 : ℝ)
  | 52 => (69 / 80 : ℝ)
  | 53 => (1049 / 1250 : ℝ)
  | 54 => (8161 / 10000 : ℝ)
  | 55 => (7931 / 10000 : ℝ)
  | 56 => (7703 / 10000 : ℝ)
  | 57 => (7477 / 10000 : ℝ)
  | 58 => (7253 / 10000 : ℝ)
  | 59 => (879 / 1250 : ℝ)
  | 60 => (3407 / 5000 : ℝ)
  | 61 => (6597 / 10000 : ℝ)
  | 62 => (399 / 625 : ℝ)
  | 63 => (3087 / 5000 : ℝ)
  | 64 => (5967 / 10000 : ℝ)
  | 65 => (2881 / 5000 : ℝ)
  | 66 => (5561 / 10000 : ℝ)
  | 67 => (1341 / 2500 : ℝ)
  | 68 => (5171 / 10000 : ℝ)
  | 69 => (249 / 500 : ℝ)
  | 70 => (2397 / 5000 : ℝ)
  | 71 => (1153 / 2500 : ℝ)
  | 72 => (4433 / 10000 : ℝ)
  | 73 => (4259 / 10000 : ℝ)
  | 74 => (511 / 1250 : ℝ)
  | 75 => (1961 / 5000 : ℝ)
  | 76 => (3759 / 10000 : ℝ)
  | 77 => (3601 / 10000 : ℝ)
  | 78 => (3447 / 10000 : ℝ)
  | 79 => (3297 / 10000 : ℝ)
  | 80 => (3151 / 10000 : ℝ)
  | 81 => (301 / 1000 : ℝ)
  | 82 => (359 / 1250 : ℝ)
  | 83 => (2739 / 10000 : ℝ)
  | 84 => (261 / 1000 : ℝ)
  | 85 => (497 / 2000 : ℝ)
  | 86 => (473 / 2000 : ℝ)
  | 87 => (281 / 1250 : ℝ)
  | 88 => (427 / 2000 : ℝ)
  | 89 => (2027 / 10000 : ℝ)
  | 90 => (961 / 5000 : ℝ)
  | 91 => (911 / 5000 : ℝ)
  | 92 => (69 / 400 : ℝ)
  | 93 => (102 / 625 : ℝ)
  | 94 => (1543 / 10000 : ℝ)
  | 95 => (1457 / 10000 : ℝ)
  | 96 => (11 / 80 : ℝ)
  | 97 => (1297 / 10000 : ℝ)
  | 98 => (1221 / 10000 : ℝ)
  | 99 => (23 / 200 : ℝ)
  | _ => 0

theorem hpThetaTraceCertificateLower_endpoint (i : ℕ) (hi : i < 100) :
    hpThetaTraceCertificateLower i ≤
      hpThetaTraceEndpointLower
        (hpThetaTraceCertificateLeft i)
        (hpThetaTraceCertificateRight i) := by
  interval_cases i
  · have h := hpThetaTrace_energy_endpoint_0
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_1
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_2
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_3
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_4
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_5
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_6
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_7
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_8
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_9
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_10
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_11
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_12
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_13
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_14
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_15
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_16
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_17
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_18
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_19
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_20
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_21
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_22
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_23
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_24
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_25
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_26
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_27
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_28
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_29
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_30
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_31
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_32
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_33
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_34
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_35
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_36
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_37
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_38
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_39
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_40
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_41
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_42
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_43
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_44
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_45
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_46
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_47
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_48
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_49
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_50
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_51
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_52
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_53
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_54
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_55
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_56
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_57
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_58
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_59
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_60
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_61
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_62
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_63
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_64
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_65
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_66
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_67
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_68
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_69
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_70
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_71
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_72
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_73
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_74
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_75
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_76
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_77
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_78
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_79
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_80
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_81
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_82
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_83
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_84
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_85
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_86
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_87
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_88
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_89
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_90
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_91
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_92
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_93
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_94
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_95
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_96
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_97
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_98
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h
  · have h := hpThetaTrace_energy_endpoint_99
    norm_num [hpThetaTraceCertificateLower,
      hpThetaTraceCertificateLeft, hpThetaTraceCertificateRight] at h ⊢
    exact h

theorem hpThetaFirstTraceEnergy_gt_seven_hundredths :
    (7 / 100 : ℝ) < hpThetaFirstTraceEnergy := by
  classical
  have hl : ∀ i ∈ Finset.range 100,
      0 ≤ hpThetaTraceCertificateLeft i := by
    intro i hi
    unfold hpThetaTraceCertificateLeft
    positivity
  have hlr : ∀ i ∈ Finset.range 100,
      hpThetaTraceCertificateLeft i ≤
        hpThetaTraceCertificateRight i := by
    intro i hi
    unfold hpThetaTraceCertificateLeft hpThetaTraceCertificateRight
    linarith
  have hq : ∀ i ∈ Finset.range 100,
      0 ≤ hpThetaTraceCertificateLower i := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    interval_cases i <;> norm_num [hpThetaTraceCertificateLower]
  have hdis : ∀ i ∈ Finset.range 100, ∀ j ∈ Finset.range 100,
      i ≠ j →
      Disjoint
        (Set.Ioo (hpThetaTraceCertificateLeft i)
          (hpThetaTraceCertificateRight i))
        (Set.Ioo (hpThetaTraceCertificateLeft j)
          (hpThetaTraceCertificateRight j)) := by
    intro i hi j hj hij
    by_cases hlt : i < j
    · apply hpThetaTrace_intervals_disjoint
      unfold hpThetaTraceCertificateLeft hpThetaTraceCertificateRight
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact_mod_cast Nat.succ_le_of_lt hlt
    · apply Disjoint.symm
      apply hpThetaTrace_intervals_disjoint
      unfold hpThetaTraceCertificateLeft hpThetaTraceCertificateRight
      apply div_le_div_of_nonneg_right _ (by norm_num)
      have hji : j < i := by omega
      exact_mod_cast Nat.succ_le_of_lt hji
  have hbound : ∀ i ∈ Finset.range 100,
      ∀ u ∈ Set.Ioo (hpThetaTraceCertificateLeft i)
        (hpThetaTraceCertificateRight i),
      hpThetaTraceCertificateLower i ≤ hpThetaTraceFirstTerm u := by
    intro i hi u hu
    exact le_trans
      (hpThetaTraceCertificateLower_endpoint i (Finset.mem_range.mp hi))
      (hpThetaTraceEndpointLower_le_firstTerm _ _ _
        (hl i hi) (le_of_lt hu.1) (le_of_lt hu.2))
  have hsum := hpThetaTrace_finite_interval_lower_sum_le
    (Finset.range 100)
    hpThetaTraceCertificateLeft hpThetaTraceCertificateRight
    hpThetaTraceCertificateLower hl hlr hq hdis hbound
  have hnumeric :
      (7 / 100 : ℝ) <
        ∑ i ∈ Finset.range 100,
          hpThetaTraceCertificateLeft i *
            hpThetaTraceCertificateLower i ^ 2 *
            (hpThetaTraceCertificateRight i -
              hpThetaTraceCertificateLeft i) := by
    norm_num [hpThetaTraceCertificateLeft,
      hpThetaTraceCertificateRight, hpThetaTraceCertificateLower,
      Finset.sum_range_succ]
  exact lt_of_lt_of_le hnumeric hsum

#print axioms hpThetaTrace_rational_endpoint_certificate
#print axioms hpThetaTraceCertificateLower_endpoint
#print axioms hpThetaFirstTraceEnergy_gt_seven_hundredths

end HodgeProofHP
