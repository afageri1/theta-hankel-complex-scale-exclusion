import HodgeProofHP.Stage4ThetaTraceExpScaling

/-!
A concrete rational lower certificate on [1/10, 11/100].
All numerical inequalities are proved inside Lean.
-/

namespace HodgeProofHP

theorem hpThetaTrace_exp_one_fifth_lower :
    (61 / 50 : ℝ) ≤ Real.exp (1 / 5) := by
  apply hpThetaTrace_exp_lower_of_taylor (1 / 5) (61 / 50) 6
  · norm_num
  · norm_num [hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial]

theorem hpThetaTrace_exp_eleven_fiftieths_upper :
    Real.exp (11 / 50) ≤ (1247 / 1000 : ℝ) := by
  apply hpThetaTrace_exp_upper_of_taylor (11 / 50) (1247 / 1000) 8
  · norm_num
  · norm_num
  · norm_num
  · norm_num [hpThetaTraceExpTaylorUpper,
      hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial]

theorem hpThetaTrace_first_interval_endpoint_certificate :
    (5 / 4 : ℝ) ≤ hpThetaTraceEndpointLower (1 / 10) (11 / 100) := by
  have hpiLo : (157 / 50 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d2
    linarith
  have hpiHi : Real.pi ≤ (63 / 20 : ℝ) := by
    have h := Real.pi_lt_d2
    linarith
  have htLo :
      (157 / 50 : ℝ) * (61 / 50) ≤
        Real.pi * Real.exp (1 / 5) :=
    mul_le_mul hpiLo hpThetaTrace_exp_one_fifth_lower
      (by norm_num) (le_of_lt Real.pi_pos)
  have htHi :
      Real.pi * Real.exp (11 / 50) ≤
        (63 / 20 : ℝ) * (1247 / 1000) :=
    mul_le_mul hpiHi hpThetaTrace_exp_eleven_fiftieths_upper
      (Real.exp_nonneg _) (by norm_num)
  have hpoly := hpThetaTrace_scalar_polynomial_mono
    ((157 / 50 : ℝ) * (61 / 50))
    (Real.pi * Real.exp (1 / 5))
    (by norm_num) htLo
  have hpolySmall :
      0 ≤ 4 * ((157 / 50 : ℝ) * (61 / 50)) ^ 2 -
        6 * ((157 / 50 : ℝ) * (61 / 50)) := by
    norm_num
  have hpoly0 :
      0 ≤ 4 * (Real.pi * Real.exp (1 / 5)) ^ 2 -
        6 * (Real.pi * Real.exp (1 / 5)) :=
    le_trans hpolySmall hpoly
  have hnegFour :
      (100 / 273 : ℝ) ^ 4 ≤ Real.exp (-4) := by
    have h := hpThetaTrace_exp_neg_nat_mul_lower
      1 (273 / 100) ((100 / 273 : ℝ) ^ 4) 4
      (by norm_num) (by norm_num)
      hpThetaTrace_exp_one_upper (by norm_num)
    norm_num at h ⊢
    exact h
  have harg :
      -(4 : ℝ) ≤ 1 / 20 - Real.pi * Real.exp (11 / 50) := by
    linarith
  have he :
      (100 / 273 : ℝ) ^ 4 ≤
        Real.exp (1 / 20 - Real.pi * Real.exp (11 / 50)) :=
    le_trans hnegFour (Real.exp_le_exp.mpr harg)
  have htwo :
      2 * (100 / 273 : ℝ) ^ 4 ≤
        2 * Real.exp (1 / 20 - Real.pi * Real.exp (11 / 50)) :=
    mul_le_mul_of_nonneg_left he (by norm_num)
  have hproduct :=
    mul_le_mul hpoly htwo
      (show 0 ≤ 2 * (100 / 273 : ℝ) ^ 4 by norm_num)
      hpoly0
  norm_num only [hpThetaTraceEndpointLower]
  change (5 / 4 : ℝ) ≤
    (4 * (Real.pi * Real.exp (1 / 5)) ^ 2 -
      6 * (Real.pi * Real.exp (1 / 5))) *
      (2 * Real.exp (1 / 20 - Real.pi * Real.exp (11 / 50)))
  calc
    (5 / 4 : ℝ) ≤
        (4 * ((157 / 50 : ℝ) * (61 / 50)) ^ 2 -
          6 * ((157 / 50 : ℝ) * (61 / 50))) *
          (2 * (100 / 273 : ℝ) ^ 4) := by norm_num
    _ ≤ _ := hproduct

theorem hpThetaTrace_first_interval_firstTerm_lower
    (u : ℝ) (hlo : (1 / 10 : ℝ) ≤ u)
    (hhi : u ≤ (11 / 100 : ℝ)) :
    (5 / 4 : ℝ) ≤ hpThetaTraceFirstTerm u := by
  exact le_trans hpThetaTrace_first_interval_endpoint_certificate
    (hpThetaTraceEndpointLower_le_firstTerm
      (1 / 10) (11 / 100) u (by norm_num) hlo hhi)

theorem hpThetaTrace_first_interval_totalEnergy_lower :
    (1 / 640 : ℝ) ≤ hpThetaFirstTraceEnergy := by
  have h := hpThetaTraceFirstTerm_interval_lower_le_totalEnergy
    (1 / 10) (11 / 100) (5 / 4)
    (by norm_num) (by norm_num) (by norm_num)
    (fun u hu =>
      hpThetaTrace_first_interval_firstTerm_lower
        u (le_of_lt hu.1) (le_of_lt hu.2))
  norm_num at h
  exact h

#print axioms hpThetaTrace_exp_one_fifth_lower
#print axioms hpThetaTrace_exp_eleven_fiftieths_upper
#print axioms hpThetaTrace_first_interval_endpoint_certificate
#print axioms hpThetaTrace_first_interval_firstTerm_lower
#print axioms hpThetaTrace_first_interval_totalEnergy_lower

end HodgeProofHP
