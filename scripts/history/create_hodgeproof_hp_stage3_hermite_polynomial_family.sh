#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3HermitePolynomialFamily.lean <<'LEAN'
import HodgeProofHP.Stage3HermiteNonzero
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian

/-!
Polynomial candidates for the project's Hermite functions:
P₀ = 1 and Pₙ₊₁ = 2 X Pₙ - Pₙ'.
Identification with hpHermiteSchwartz is a separate theorem.
-/

namespace HodgeProofHP

noncomputable def hpHermitePolynomial : ℕ → Polynomial ℂ
  | 0 => 1
  | n + 1 =>
      Polynomial.C 2 * Polynomial.X * hpHermitePolynomial n -
        Polynomial.derivative (hpHermitePolynomial n)

theorem hpHermitePolynomial_zero :
    hpHermitePolynomial 0 = 1 := rfl

theorem hpHermitePolynomial_succ (n : ℕ) :
    hpHermitePolynomial (n + 1) =
      Polynomial.C 2 * Polynomial.X * hpHermitePolynomial n -
        Polynomial.derivative (hpHermitePolynomial n) := rfl

theorem hpHermitePolynomial_one :
    hpHermitePolynomial 1 =
      Polynomial.C 2 * Polynomial.X := by
  simp [hpHermitePolynomial]

theorem hpHermitePolynomial_succ_eval (n : ℕ) (z : ℂ) :
    (hpHermitePolynomial (n + 1)).eval z =
      2 * z * (hpHermitePolynomial n).eval z -
        (Polynomial.derivative (hpHermitePolynomial n)).eval z := by
  simp only [hpHermitePolynomial_succ, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

#print axioms hpHermitePolynomial_one
#print axioms hpHermitePolynomial_succ_eval

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3HermitePolynomialFamily.lean
lake build HodgeProofHP.Stage3HermitePolynomialFamily
