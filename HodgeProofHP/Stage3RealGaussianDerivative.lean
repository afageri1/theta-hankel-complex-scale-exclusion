import HodgeProofHP.Stage3GaussianGroundL2

/-!
The first derivative of the real Gaussian.
-/

namespace HodgeProofHP

theorem hpRealGaussian_deriv (x : ℝ) :
    deriv (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) x =
      -x * Real.exp (-(x ^ 2 / 2)) := by
  simpa [Polynomial.hermite_one] using
    (Polynomial.deriv_gaussian_eq_hermite_mul_gaussian 1 x)

#print axioms hpRealGaussian_deriv

end HodgeProofHP
