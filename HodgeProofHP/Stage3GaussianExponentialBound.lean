import HodgeProofHP.Stage3GaussianWeightedMoments

/-! A Gaussian bound for exponential weights. -/

namespace HodgeProofHP

theorem hpGaussian_exponential_exponent_bound (a x : ℝ) :
    a * |x| - x ^ 2 / 2 ≤ a ^ 2 - x ^ 2 / 4 := by
  have hx : |x| ^ 2 = x ^ 2 := sq_abs x
  have hsq : 0 ≤ (|x| / 2 - a) ^ 2 :=
    sq_nonneg (|x| / 2 - a)
  nlinarith

theorem hpGaussian_exponential_weight_bound (a x : ℝ) :
    Real.exp (a * |x|) * Real.exp (-(x ^ 2 / 2)) ≤
      Real.exp (a ^ 2) * Real.exp (-(x ^ 2 / 4)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := hpGaussian_exponential_exponent_bound a x
  linarith

#print axioms hpGaussian_exponential_exponent_bound
#print axioms hpGaussian_exponential_weight_bound

end HodgeProofHP
