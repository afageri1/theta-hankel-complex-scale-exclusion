import HodgeProofHP.Stage4ThetaTraceExpCertificates

/-!
Scaling exponential upper certificates and obtaining lower certificates
for negative exponents by inversion.
-/

namespace HodgeProofHP

theorem hpThetaTrace_exp_nat_mul_upper
    (x U : ℝ) (hU : 0 ≤ U)
    (hupper : Real.exp x ≤ U) (n : ℕ) :
    Real.exp ((n : ℝ) * x) ≤ U ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have harg :
          ((n + 1 : ℕ) : ℝ) * x = (n : ℝ) * x + x := by
        push_cast
        ring
      rw [harg, Real.exp_add, pow_succ]
      exact mul_le_mul ih hupper
        (Real.exp_nonneg x) (pow_nonneg hU n)

theorem hpThetaTrace_exp_neg_lower_of_upper
    (x U q : ℝ) (hq : 0 ≤ q)
    (hupper : Real.exp x ≤ U)
    (hcert : q * U ≤ 1) :
    q ≤ Real.exp (-x) := by
  rw [Real.exp_neg, inv_eq_one_div]
  apply (le_div_iff₀ (Real.exp_pos x)).mpr
  exact le_trans
    (mul_le_mul_of_nonneg_left hupper hq) hcert

theorem hpThetaTrace_exp_neg_nat_mul_lower
    (x U q : ℝ) (n : ℕ) (hU : 0 ≤ U) (hq : 0 ≤ q)
    (hupper : Real.exp x ≤ U)
    (hcert : q * U ^ n ≤ 1) :
    q ≤ Real.exp (-((n : ℝ) * x)) := by
  exact hpThetaTrace_exp_neg_lower_of_upper
    ((n : ℝ) * x) (U ^ n) q hq
    (hpThetaTrace_exp_nat_mul_upper x U hU hupper n)
    hcert

theorem hpThetaTrace_exp_neg_one_lower :
    (100 / 273 : ℝ) ≤ Real.exp (-1) := by
  apply hpThetaTrace_exp_neg_lower_of_upper
    1 (273 / 100) (100 / 273)
  · norm_num
  · exact hpThetaTrace_exp_one_upper
  · norm_num

theorem hpThetaTrace_exp_neg_half_lower :
    (20 / 33 : ℝ) ≤ Real.exp (-(1 / 2)) := by
  apply hpThetaTrace_exp_neg_lower_of_upper
    (1 / 2) (165 / 100) (20 / 33)
  · norm_num
  · exact hpThetaTrace_exp_half_upper
  · norm_num

#print axioms hpThetaTrace_exp_nat_mul_upper
#print axioms hpThetaTrace_exp_neg_lower_of_upper
#print axioms hpThetaTrace_exp_neg_nat_mul_lower
#print axioms hpThetaTrace_exp_neg_one_lower
#print axioms hpThetaTrace_exp_neg_half_lower

end HodgeProofHP
