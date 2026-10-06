import HodgeProofHP.Stage3ComplexGaussianSecondDeriv
import HodgeProofHP.Stage3GaussianPointwiseAction

/-!
The complex Gaussian satisfies the harmonic-oscillator equation
pointwise on the real line.
-/

namespace HodgeProofHP

theorem hpComplexGaussian_harmonic_pointwise (x : ℝ) :
    -deriv (deriv (hpComplexGaussianSchwartz : ℝ → ℂ)) x
      + hpQuadraticPotential x • hpComplexGaussianSchwartz x
      = hpComplexGaussianSchwartz x := by
  have hvalue :
      hpComplexGaussianSchwartz x =
        (↑(Real.exp (-(x ^ 2 / 2))) : ℂ) := by
    simp only [hpComplexGaussianSchwartz,
      SchwartzMap.postcompCLM_apply]
    rfl
  rw [hpComplexGaussianSchwartz_second_deriv_cast, hvalue]
  have hreal := congrArg (fun r : ℝ => (↑r : ℂ))
    (hpRealGaussian_harmonic_pointwise x)
  simpa [hpQuadraticPotential, Complex.real_smul] using hreal

#print axioms hpComplexGaussian_harmonic_pointwise

end HodgeProofHP
