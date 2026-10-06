import HodgeProofHP.Stage3GaussianProductCreation
import Mathlib.Analysis.Complex.RealDeriv

/-!
Identify the Schwartz Hermite family pointwise with
the polynomial family multiplied by the Gaussian.
-/

namespace HodgeProofHP

theorem hpPolynomial_real_hasDerivAt
    (p : Polynomial ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => p.eval (y : ℂ))
      (Polynomial.derivative p |>.eval (x : ℂ)) x := by
  exact (p.hasDerivAt (x : ℂ)).comp_ofReal

theorem hpHermiteSchwartz_polynomial_apply (n : ℕ) (x : ℝ) :
    hpHermiteSchwartz n x =
      (hpHermitePolynomial n).eval (x : ℂ) *
        hpGaussianGroundFunction x := by
  induction n generalizing x with
  | zero =>
      rw [hpHermiteSchwartz_zero, hpComplexGaussianSchwartz_apply,
        hpHermitePolynomial_zero]
      simp
  | succ n ih =>
      have hfun :
          (hpHermiteSchwartz n : ℝ → ℂ) =
            (fun y : ℝ =>
              (hpHermitePolynomial n).eval (y : ℂ) *
                hpGaussianGroundFunction y) := by
        funext y
        exact ih y
      rw [hpHermiteSchwartz_succ_apply]
      simp only [hfun]
      change
        (x : ℂ) *
            ((hpHermitePolynomial n).eval (x : ℂ) *
              hpGaussianGroundFunction x) -
          deriv
            (fun y : ℝ =>
              (hpHermitePolynomial n).eval (y : ℂ) *
                hpGaussianGroundFunction y) x =
        (hpHermitePolynomial (n + 1)).eval (x : ℂ) *
          hpGaussianGroundFunction x
      rw [hpGaussianProduct_creation
        (fun y : ℝ => (hpHermitePolynomial n).eval (y : ℂ)) x
        (hpPolynomial_real_hasDerivAt
          (hpHermitePolynomial n) x).differentiableAt]
      rw [(hpPolynomial_real_hasDerivAt
        (hpHermitePolynomial n) x).deriv,
        hpHermitePolynomial_succ_eval]

#print axioms hpPolynomial_real_hasDerivAt
#print axioms hpHermiteSchwartz_polynomial_apply

end HodgeProofHP
