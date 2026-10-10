#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3GaussianFirstDerivativeBound.lean <<'LEAN'
import HodgeProofHP.Stage3GaussianSmooth
import HodgeProofHP.Stage3RealGaussianDerivative

/-! Polynomially weighted bound for the first derivative of the real Gaussian. -/

namespace HodgeProofHP

theorem hpRealGaussian_firstDerivative_weighted_bounded (k : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ,
      |x| ^ k *
        |deriv (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) x| ≤ C := by
  obtain ⟨C, hC⟩ := hpRealGaussian_weighted_bounded (k + 1)
  refine ⟨C, fun x => ?_⟩
  have hderiv :
      |deriv (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) x| =
        |x| * Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
    rw [hpRealGaussian_deriv]
    rw [abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]
    congr 1
    ring
  calc
    |x| ^ k *
        |deriv (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) x| =
      |x| ^ (k + 1) * Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
        rw [hderiv, pow_succ]
        ring
    _ ≤ C := hC x

#print axioms hpRealGaussian_firstDerivative_weighted_bounded

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3GaussianFirstDerivativeBound.lean
lake build HodgeProofHP.Stage3GaussianFirstDerivativeBound
