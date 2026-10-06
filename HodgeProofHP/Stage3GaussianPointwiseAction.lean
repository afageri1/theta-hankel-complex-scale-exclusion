import HodgeProofHP.Stage3RealGaussianDerivative

/-!
The harmonic-oscillator equation for the real Gaussian as a pointwise
identity. No operator-domain membership is asserted here.
-/

namespace HodgeProofHP

private theorem hpHermite_two :
    Polynomial.hermite 2 = Polynomial.X ^ 2 - 1 := by
  rw [show (2 : ℕ) = 1 + 1 by norm_num,
    Polynomial.hermite_succ, Polynomial.hermite_one]
  simp [pow_two, Polynomial.derivative_X]

theorem hpRealGaussian_second_deriv (x : ℝ) :
    (deriv^[2]) (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) x =
      (x ^ 2 - 1) * Real.exp (-(x ^ 2 / 2)) := by
  simpa [hpHermite_two, pow_two] using
    (Polynomial.deriv_gaussian_eq_hermite_mul_gaussian 2 x)

theorem hpRealGaussian_harmonic_pointwise (x : ℝ) :
    -(deriv^[2]) (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) x
      + x ^ 2 * Real.exp (-(x ^ 2 / 2))
      = Real.exp (-(x ^ 2 / 2)) := by
  rw [hpRealGaussian_second_deriv]
  ring

#print axioms hpRealGaussian_harmonic_pointwise

end HodgeProofHP
