import HodgeProofHP.Stage3GaussianWeightedExponentialL1

/-! Vanishing integrals of finite exponential Taylor sums. -/

open MeasureTheory
open scoped BigOperators

namespace HodgeProofHP

noncomputable def hpGaussianMomentTaylorTerm
    (v : HPSpace) (z : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  (z ^ n / (n.factorial : ℂ)) *
    ((x : ℂ) ^ n * hpGaussianWeightedL2Function v x)

theorem hpGaussianMomentTaylorTerm_integrable
    (v : HPSpace) (z : ℂ) (n : ℕ) :
    Integrable (hpGaussianMomentTaylorTerm v z n) volume := by
  exact
    (hpGaussianWeightedL2Function_moment_integrable v n).const_mul
      (z ^ n / (n.factorial : ℂ))

theorem hpGaussianMomentTaylorTerm_integral_eq_zero
    (v : HPSpace) (hv : v ∈ hpHermiteL2Span.orthogonal)
    (z : ℂ) (n : ℕ) :
    (∫ x : ℝ, hpGaussianMomentTaylorTerm v z n x) = 0 := by
  unfold hpGaussianMomentTaylorTerm
  rw [integral_const_mul,
    hpGaussianWeightedL2Function_moment_eq_zero v hv n, mul_zero]

theorem hpGaussianMomentTaylorSum_integral_eq_zero
    (v : HPSpace) (hv : v ∈ hpHermiteL2Span.orthogonal)
    (z : ℂ) (N : ℕ) :
    (∫ x : ℝ,
      ∑ n ∈ Finset.range N, hpGaussianMomentTaylorTerm v z n x) = 0 := by
  rw [integral_finset_sum (Finset.range N)
    (fun n _ => hpGaussianMomentTaylorTerm_integrable v z n)]
  simp only [hpGaussianMomentTaylorTerm_integral_eq_zero v hv,
    Finset.sum_const_zero]

#print axioms hpGaussianMomentTaylorTerm_integrable
#print axioms hpGaussianMomentTaylorTerm_integral_eq_zero
#print axioms hpGaussianMomentTaylorSum_integral_eq_zero

end HodgeProofHP
