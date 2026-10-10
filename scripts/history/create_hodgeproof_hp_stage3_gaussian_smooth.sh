#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3GaussianSmooth.lean <<'LEAN'
import HodgeProofHP.Stage3ComplexGaussianBound
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
Smoothness of the complex Gaussian. Weighted bounds for all derivatives
are still required to establish Schwartz membership.
-/

namespace HodgeProofHP

open scoped ContDiff

theorem hpGaussianGroundFunction_contDiff :
    ContDiff ℝ ∞ hpGaussianGroundFunction := by
  have hreal :
      ContDiff ℝ ∞
        (fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by
    fun_prop
  have hcomplex :
      ContDiff ℝ ∞
        (fun x : ℝ => (Real.exp (-(1 / 2 : ℝ) * x ^ 2) : ℂ)) := by
    have h := Complex.ofRealCLM.contDiff.comp hreal
    convert h using 1
    funext x
    simp
  have hfun :
      hpGaussianGroundFunction =
        (fun x : ℝ => (Real.exp (-(1 / 2 : ℝ) * x ^ 2) : ℂ)) := by
    funext x
    simp only [hpGaussianGroundFunction, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hfun]
  exact hcomplex

#print axioms hpGaussianGroundFunction_contDiff

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3GaussianSmooth.lean
lake build HodgeProofHP.Stage3GaussianSmooth
