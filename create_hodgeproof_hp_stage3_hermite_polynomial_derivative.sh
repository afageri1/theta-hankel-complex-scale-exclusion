#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3HermitePolynomialDerivative.lean <<'LEAN'
import HodgeProofHP.Stage3HermitePolynomialIdentification
import Mathlib.Algebra.Polynomial.Derivative

/-! Formal derivative identities for the Hermite polynomial family. -/

namespace HodgeProofHP

theorem hpPolynomial_derivative_creation (p : Polynomial ℂ) :
    Polynomial.derivative
        (Polynomial.C 2 * Polynomial.X * p -
          Polynomial.derivative p) =
      Polynomial.C 2 * Polynomial.X * Polynomial.derivative p -
        Polynomial.derivative (Polynomial.derivative p) +
        Polynomial.C 2 * p := by
  simp only [Polynomial.derivative_sub, Polynomial.derivative_mul,
    Polynomial.derivative_C, Polynomial.derivative_X,
    zero_mul, zero_add, mul_one]
  ring

theorem hpHermitePolynomial_derivative_succ (n : ℕ) :
    Polynomial.derivative (hpHermitePolynomial (n + 1)) =
      Polynomial.C (2 * (n : ℂ) + 2) *
        hpHermitePolynomial n := by
  induction n with
  | zero =>
      simp [hpHermitePolynomial]
  | succ n ih =>
      rw [hpHermitePolynomial_succ,
        hpPolynomial_derivative_creation, ih]
      simp only [Polynomial.derivative_mul,
        Polynomial.derivative_C, zero_mul, zero_add]
      have hcoeff :
          Polynomial.C (2 * ((n + 1 : ℕ) : ℂ) + 2) =
            Polynomial.C (2 * (n : ℂ) + 2) +
              Polynomial.C (2 : ℂ) := by
        rw [← Polynomial.C_add]
        congr 1
        push_cast
        ring
      rw [hcoeff]
      simp only [hpHermitePolynomial_succ]
      ring

#print axioms hpPolynomial_derivative_creation
#print axioms hpHermitePolynomial_derivative_succ

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3HermitePolynomialDerivative.lean
lake build HodgeProofHP.Stage3HermitePolynomialDerivative
