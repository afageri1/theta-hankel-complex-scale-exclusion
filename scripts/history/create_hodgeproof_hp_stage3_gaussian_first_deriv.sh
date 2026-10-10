#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3GaussianFirstDeriv.lean <<'LEAN'
import HodgeProofHP.Stage3HermitePolynomialFamily

/-!
First derivative of the complex Gaussian ground function,
obtained by casting the real Gaussian derivative.
-/

namespace HodgeProofHP

theorem hpGaussianGroundFunction_deriv (x : ℝ) :
    deriv hpGaussianGroundFunction x =
      -(x : ℂ) * hpGaussianGroundFunction x := by
  have hfun :
      hpGaussianGroundFunction =
        (fun y : ℝ => (Real.exp (-(y ^ 2 / 2)) : ℂ)) := by
    funext y
    simp only [hpGaussianGroundFunction, Complex.ofReal_exp]
    congr 1; push_cast; ring
  have hreal :
      deriv (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) x =
        -x * Real.exp (-(x ^ 2 / 2)) := by
    simpa [Polynomial.hermite_one] using
      (Polynomial.deriv_gaussian_eq_hermite_mul_gaussian 1 x)
  have hdiff :
      DifferentiableAt ℝ
        (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) x := by
    fun_prop
  have hcast := HasDerivAt.ofReal_comp hdiff.hasDerivAt
  rw [hfun]
  simpa only [hreal, Complex.ofReal_mul, Complex.ofReal_neg] using
    hcast.deriv

#print axioms hpGaussianGroundFunction_deriv

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3GaussianFirstDeriv.lean
lake build HodgeProofHP.Stage3GaussianFirstDeriv
