#!/usr/bin/env bash
set -euo pipefail

for file in \
  HodgeProofHP/Stage3GaussianFirstDeriv.lean \
  create_hodgeproof_hp_stage3_gaussian_first_deriv.sh
do
  sed -i 's/congr 1 <;> push_cast <;> ring/congr 1; push_cast; ring/' "$file"
done

lake env lean HodgeProofHP/Stage3GaussianFirstDeriv.lean
lake build HodgeProofHP.Stage3GaussianFirstDeriv

cat > HodgeProofHP/Stage3GaussianProductCreation.lean <<'LEAN'
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
LEAN

lake env lean HodgeProofHP/Stage3GaussianProductCreation.lean
lake build HodgeProofHP.Stage3GaussianProductCreation

printf '\n=== Polynomial derivative API ===\n'
rg -n -C 3 'hasDerivAt|deriv_aeval|deriv_eval' \
  .lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv/Polynomial.lean \
  | head -100 || true

printf '\n=== Derivative composition with ofReal ===\n'
rg -n -C 3 'comp_ofReal|hasDerivAt.*ofReal|deriv.*ofReal' \
  .lake/packages/mathlib/Mathlib/Analysis/Calculus/Deriv \
  | head -100 || true
