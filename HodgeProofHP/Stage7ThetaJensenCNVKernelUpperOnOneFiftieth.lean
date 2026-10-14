/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCNVKernelLowerOnOneFiftieth
import HodgeProofHP.Stage5ThetaJensenKernelBounds

/-!
# Uniform upper bound for the actual kernel on [0, 1/50]

Two rational endpoint certificates use the existing analytic first-term upper
bound, including the whole remaining Gaussian series. Taylor sums certify all
exponential estimates. CNV positivity is a separate subsequent obligation.
-/
noncomputable section
namespace HodgeProofHP

theorem hpThetaCNV_endpointUpper_le_two_of_bounds (l r U L W : ℝ)
    (hr : 0 ≤ r) (hU : 3 ≤ U)
    (hqU : Real.pi * Real.exp (2 * r) ≤ U)
    (hLq : L ≤ Real.pi * Real.exp (2 * l))
    (hexp : Real.exp (r / 2 - L) ≤ W)
    (hnum : (12183 / 12151 : ℝ) * ((4 * U ^ 2 - 6 * U) * (2 * W)) ≤ 2) :
    hpThetaJensenKernelEndpointUpper l r ≤ 2 := by
  have hpoly := hpThetaTrace_scalar_polynomial_mono
    (Real.pi * Real.exp (2 * r)) U (hpThetaTrace_pi_exp_ge_three r hr) hqU
  have hpolyU : 0 ≤ 4 * U ^ 2 - 6 * U := by
    nlinarith [sq_nonneg (U - 3)]
  have he : 2 * Real.exp (r / 2 - Real.pi * Real.exp (2 * l)) ≤ 2 * W := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact (Real.exp_le_exp.mpr (by linarith)).trans hexp
  unfold hpThetaJensenKernelEndpointUpper
  exact (mul_le_mul_of_nonneg_left
    (mul_le_mul hpoly he (by positivity) hpolyU) (by norm_num)).trans hnum

theorem hpThetaCNV_exp_oneFiftieth_upper :
    Real.exp (1 / 50 : ℝ) ≤ (1021 / 1000 : ℝ) := by
  exact hpThetaTrace_exp_upper_of_taylor (1 / 50) (1021 / 1000) 6
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial])

theorem hpThetaCNV_exp_oneTwentyFifth_upper :
    Real.exp (1 / 25 : ℝ) ≤ (52041 / 50000 : ℝ) := by
  exact hpThetaTrace_exp_upper_of_taylor (1 / 25) (52041 / 50000) 6
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [hpThetaTraceExpTaylorUpper, hpThetaTraceExpTaylorSum,
      Finset.sum_range_succ, Nat.factorial])

theorem hpThetaCNV_exp_neg_firstHalf_upper :
    Real.exp (-(6273 / 2000 : ℝ)) ≤ (1 / 23 : ℝ) := by
  have hv : (23 : ℝ) ≤ Real.exp (6273 / 2000 : ℝ) := by
    exact hpThetaTrace_exp_lower_of_taylor (6273 / 2000) 23 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := mul_le_mul_of_nonneg_right hv
    (Real.exp_nonneg (-(6273 / 2000 : ℝ)))
  have hid : Real.exp (6273 / 2000 : ℝ) * Real.exp (-(6273 / 2000 : ℝ)) = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [hid] at h
  linarith

theorem hpThetaCNV_exp_neg_secondHalf_upper :
    Real.exp (-(319 / 100 : ℝ)) ≤ (1 / 24 : ℝ) := by
  have hv : (24 : ℝ) ≤ Real.exp (319 / 100 : ℝ) := by
    exact hpThetaTrace_exp_lower_of_taylor (319 / 100) 24 12
      (by norm_num)
      (by norm_num [hpThetaTraceExpTaylorSum, Finset.sum_range_succ, Nat.factorial])
  have h := mul_le_mul_of_nonneg_right hv
    (Real.exp_nonneg (-(319 / 100 : ℝ)))
  have hid : Real.exp (319 / 100 : ℝ) * Real.exp (-(319 / 100 : ℝ)) = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [hid] at h
  linarith

theorem hpThetaCNV_endpointUpper_firstHalf_le_two :
    hpThetaJensenKernelEndpointUpper 0 (1 / 100) ≤ 2 := by
  have hpiL : (31415 / 10000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d4
    linarith
  have hpiU : Real.pi ≤ (3927 / 1250 : ℝ) := by
    have h := Real.pi_lt_d4
    linarith
  have he : Real.exp (2 * (1 / 100 : ℝ)) ≤ (1021 / 1000 : ℝ) := by
    convert hpThetaCNV_exp_oneFiftieth_upper using 1 <;> norm_num
  have hqU : Real.pi * Real.exp (2 * (1 / 100 : ℝ)) ≤ (321 / 100 : ℝ) := by
    calc
      _ ≤ (3927 / 1250 : ℝ) * (1021 / 1000) :=
        mul_le_mul hpiU he (Real.exp_nonneg _) (by norm_num)
      _ ≤ _ := by norm_num
  have hLq : (31415 / 10000 : ℝ) ≤ Real.pi * Real.exp (2 * (0 : ℝ)) := by
    simpa only [mul_zero, Real.exp_zero, mul_one] using hpiL
  have hexp : Real.exp ((1 / 100 : ℝ) / 2 - 31415 / 10000) ≤ (1 / 23 : ℝ) := by
    convert hpThetaCNV_exp_neg_firstHalf_upper using 1 <;> norm_num
  exact hpThetaCNV_endpointUpper_le_two_of_bounds
    0 (1 / 100) (321 / 100) (31415 / 10000) (1 / 23)
    (by norm_num) (by norm_num) hqU hLq hexp (by norm_num)

theorem hpThetaCNV_endpointUpper_secondHalf_le_two :
    hpThetaJensenKernelEndpointUpper (1 / 100) (1 / 50) ≤ 2 := by
  have hpiL : (31415 / 10000 : ℝ) ≤ Real.pi := by
    have h := Real.pi_gt_d4
    linarith
  have hpiU : Real.pi ≤ (3927 / 1250 : ℝ) := by
    have h := Real.pi_lt_d4
    linarith
  have he : Real.exp (2 * (1 / 50 : ℝ)) ≤ (52041 / 50000 : ℝ) := by
    convert hpThetaCNV_exp_oneTwentyFifth_upper using 1 <;> norm_num
  have hqU : Real.pi * Real.exp (2 * (1 / 50 : ℝ)) ≤ (327 / 100 : ℝ) := by
    calc
      _ ≤ (3927 / 1250 : ℝ) * (52041 / 50000) :=
        mul_le_mul hpiU he (Real.exp_nonneg _) (by norm_num)
      _ ≤ _ := by norm_num
  have heL : (51 / 50 : ℝ) ≤ Real.exp (2 * (1 / 100 : ℝ)) := by
    convert Real.add_one_le_exp (1 / 50 : ℝ) using 1 <;> norm_num
  have hLq : (16 / 5 : ℝ) ≤ Real.pi * Real.exp (2 * (1 / 100 : ℝ)) := by
    calc
      _ ≤ (31415 / 10000 : ℝ) * (51 / 50) := by norm_num
      _ ≤ _ := mul_le_mul hpiL heL (by norm_num) Real.pi_pos.le
  have hexp : Real.exp ((1 / 50 : ℝ) / 2 - 16 / 5) ≤ (1 / 24 : ℝ) := by
    convert hpThetaCNV_exp_neg_secondHalf_upper using 1 <;> norm_num
  exact hpThetaCNV_endpointUpper_le_two_of_bounds
    (1 / 100) (1 / 50) (327 / 100) (16 / 5) (1 / 24)
    (by norm_num) (by norm_num) hqU hLq hexp (by norm_num)

theorem hpThetaPhi_le_two_on_oneFiftieth (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 50)) :
    hpRiemannThetaDifferentialKernel t ≤ 2 := by
  by_cases hmid : t ≤ (1 / 100 : ℝ)
  · exact (hpThetaJensenKernel_le_endpointUpper 0 (1 / 100) t
      (by norm_num) ht.1 hmid).trans hpThetaCNV_endpointUpper_firstHalf_le_two
  · exact (hpThetaJensenKernel_le_endpointUpper (1 / 100) (1 / 50) t
      (by norm_num) (lt_of_not_ge hmid).le ht.2).trans
      hpThetaCNV_endpointUpper_secondHalf_le_two

#print axioms hpThetaCNV_endpointUpper_le_two_of_bounds
#print axioms hpThetaCNV_exp_oneFiftieth_upper
#print axioms hpThetaCNV_exp_oneTwentyFifth_upper
#print axioms hpThetaCNV_exp_neg_firstHalf_upper
#print axioms hpThetaCNV_exp_neg_secondHalf_upper
#print axioms hpThetaCNV_endpointUpper_firstHalf_le_two
#print axioms hpThetaCNV_endpointUpper_secondHalf_le_two
#print axioms hpThetaPhi_le_two_on_oneFiftieth
end HodgeProofHP

