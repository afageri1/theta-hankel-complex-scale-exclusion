import HodgeProofHP.Stage3GaussianFirstDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
Creation action on a differentiable function times the Gaussian:
x (p g) - (p g)' = (2 x p - p') g.
-/

namespace HodgeProofHP

theorem hpGaussianGroundFunction_hasDerivAt (x : ℝ) :
    HasDerivAt hpGaussianGroundFunction
      (-(x : ℂ) * hpGaussianGroundFunction x) x := by
  have hfun :
      (hpComplexGaussianSchwartz : ℝ → ℂ) =
        hpGaussianGroundFunction := by
    funext y
    exact hpComplexGaussianSchwartz_apply y
  have hdiff :
      DifferentiableAt ℝ hpGaussianGroundFunction x := by
    rw [← hfun]
    exact hpComplexGaussianSchwartz.differentiableAt
  rw [← hpGaussianGroundFunction_deriv]
  exact hdiff.hasDerivAt

theorem hpGaussianProduct_creation
    (p : ℝ → ℂ) (x : ℝ)
    (hp : DifferentiableAt ℝ p x) :
    (x : ℂ) * (p x * hpGaussianGroundFunction x) -
        deriv (fun y => p y * hpGaussianGroundFunction y) x =
      (2 * (x : ℂ) * p x - deriv p x) *
        hpGaussianGroundFunction x := by
  rw [deriv_fun_mul hp
    (hpGaussianGroundFunction_hasDerivAt x).differentiableAt]
  rw [hpGaussianGroundFunction_deriv]
  ring

#print axioms hpGaussianGroundFunction_hasDerivAt
#print axioms hpGaussianProduct_creation

end HodgeProofHP
