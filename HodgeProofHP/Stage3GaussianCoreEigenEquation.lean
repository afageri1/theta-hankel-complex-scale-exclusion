import HodgeProofHP.Stage3ComplexGaussianPointwiseAction
import HodgeProofHP.Stage3HarmonicActionAE

/-!
The harmonic core operator maps the complex Gaussian Schwartz
realization to the existing Gaussian element of L².
-/

namespace HodgeProofHP

theorem hpComplexGaussian_core_eigen_equation :
    HPHarmonicCoreOperator.toFun
        (hpSchwartzCoreEquiv hpComplexGaussianSchwartz) =
      hpGaussianGroundL2 := by
  apply MeasureTheory.Lp.ext
  filter_upwards
    [hpHarmonicCoreOperator_apply_ae hpComplexGaussianSchwartz,
      hpGaussianGroundL2_apply_ae] with x hOperator hGaussian
  calc
    ((HPHarmonicCoreOperator.toFun
        (hpSchwartzCoreEquiv hpComplexGaussianSchwartz) : HPSpace)
        : ℝ → ℂ) x =
        -deriv (deriv
          (hpComplexGaussianSchwartz : ℝ → ℂ)) x
          + hpQuadraticPotential x • hpComplexGaussianSchwartz x :=
            hOperator
    _ = hpComplexGaussianSchwartz x :=
      hpComplexGaussian_harmonic_pointwise x
    _ = hpGaussianGroundFunction x :=
      hpComplexGaussianSchwartz_apply x
    _ = (hpGaussianGroundL2 : ℝ → ℂ) x :=
      hGaussian.symm

#print axioms hpComplexGaussian_core_eigen_equation

end HodgeProofHP
