import HodgeProofHP.Stage3HermiteOrthogonalIntegrals

/-!
Gaussian-weighted L2 representatives are integrable and have vanishing
moments when orthogonal to the Hermite span.
-/

namespace HodgeProofHP

open MeasureTheory

theorem hpGaussianGroundFunction_eq_real (x : ℝ) :
    hpGaussianGroundFunction x =
      (Real.exp (-(x ^ 2 / 2)) : ℂ) := by
  simp only [hpGaussianGroundFunction, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

noncomputable def hpGaussianWeightedL2Function
    (v : HPSpace) (x : ℝ) : ℂ :=
  hpGaussianGroundFunction x * v x

theorem hpGaussian_monomial_inner
    (n : ℕ) (x : ℝ) (z : ℂ) :
    inner ℂ ((x : ℂ) ^ n * hpGaussianGroundFunction x) z =
      (x : ℂ) ^ n * (hpGaussianGroundFunction x * z) := by
  have hx : (starRingEnd ℂ) (x : ℂ) = (x : ℂ) :=
    Complex.conj_ofReal x
  have hg :
      (starRingEnd ℂ) (hpGaussianGroundFunction x) =
        hpGaussianGroundFunction x := by
    rw [hpGaussianGroundFunction_eq_real]
    exact Complex.conj_ofReal _
  rw [RCLike.inner_apply', map_mul, map_pow, hx, hg]
  ring

theorem hpGaussianWeightedL2Function_integrable (v : HPSpace) :
    Integrable (hpGaussianWeightedL2Function v) volume := by
  change Integrable
    (fun x : ℝ => hpGaussianGroundFunction x * v x) volume
  simpa only [Polynomial.eval_one, one_mul] using
    hpPolynomialGaussian_mul_L2_integrable
      (1 : Polynomial ℂ) v

theorem hpGaussianWeightedL2Function_moment_integrable
    (v : HPSpace) (n : ℕ) :
    Integrable
      (fun x : ℝ =>
        (x : ℂ) ^ n * hpGaussianWeightedL2Function v x)
      volume := by
  simpa [hpGaussianWeightedL2Function, mul_assoc] using
    hpPolynomialGaussian_mul_L2_integrable
      ((Polynomial.X : Polynomial ℂ) ^ n) v

theorem hpGaussianWeightedL2Function_moment_eq_zero
    (v : HPSpace) (hv : v ∈ hpHermiteL2Span.orthogonal)
    (n : ℕ) :
    (∫ x : ℝ,
      (x : ℂ) ^ n * hpGaussianWeightedL2Function v x) = 0 := by
  simpa only [hpGaussian_monomial_inner,
    hpGaussianWeightedL2Function] using
    hpHermite_orthogonal_monomial_integral_eq_zero v hv n

#print axioms hpGaussianGroundFunction_eq_real
#print axioms hpGaussianWeightedL2Function_integrable
#print axioms hpGaussianWeightedL2Function_moment_integrable
#print axioms hpGaussianWeightedL2Function_moment_eq_zero

end HodgeProofHP
