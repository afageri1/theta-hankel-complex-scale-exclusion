#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3ComplexGaussianSecondDeriv.lean <<'LEAN'
import HodgeProofHP.Stage3GaussianL2Domain
import Mathlib.Analysis.Complex.RealDeriv

/-!
The second real derivative of the complex Gaussian is the complex
cast of the second derivative of the real Gaussian.
-/

namespace HodgeProofHP

open scoped ContDiff

theorem hpComplexGaussianSchwartz_second_deriv_cast (x : ℝ) :
    deriv (deriv (hpComplexGaussianSchwartz : ℝ → ℂ)) x =
      (↑((deriv^[2])
        (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) x) : ℂ) := by
  let g : ℝ → ℝ := fun y => Real.exp (-(y ^ 2 / 2))

  have hsmooth : ContDiff ℝ ∞ g := by
    dsimp [g]
    fun_prop
  have hd0 : Differentiable ℝ g :=
    hsmooth.differentiable (by simp)
  have hd1 : Differentiable ℝ (deriv g) := by
    simpa only [iteratedDeriv_one] using
      (hsmooth.differentiable_iteratedDeriv 1 (by simp))

  have hfun : (hpComplexGaussianSchwartz : ℝ → ℂ) =
      (fun y : ℝ => (↑(g y) : ℂ)) := by
    funext y
    simp only [hpComplexGaussianSchwartz,
      SchwartzMap.postcompCLM_apply]
    rfl

  have hfirst :
      deriv (fun y : ℝ => (↑(g y) : ℂ)) =
        (fun y : ℝ => (↑(deriv g y) : ℂ)) := by
    funext y
    exact (HasDerivAt.ofReal_comp ((hd0 y).hasDerivAt)).deriv

  have hsecond :
      deriv (fun y : ℝ => (↑(deriv g y) : ℂ)) x =
        (↑(deriv (deriv g) x) : ℂ) :=
    (HasDerivAt.ofReal_comp ((hd1 x).hasDerivAt)).deriv

  rw [hfun, hfirst]
  change deriv (fun y : ℝ => (↑(deriv g y) : ℂ)) x =
    (↑(deriv (deriv g) x) : ℂ)
  exact hsecond

#print axioms hpComplexGaussianSchwartz_second_deriv_cast

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3ComplexGaussianSecondDeriv.lean
lake build HodgeProofHP.Stage3ComplexGaussianSecondDeriv
