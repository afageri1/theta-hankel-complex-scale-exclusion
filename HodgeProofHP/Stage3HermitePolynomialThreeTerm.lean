import HodgeProofHP.Stage3HermitePolynomialDerivative

/-!
Three-term recurrence for the Hermite polynomial family.
-/

namespace HodgeProofHP

theorem hpHermitePolynomial_three_term (n : ℕ) :
    Polynomial.C 2 * Polynomial.X *
        hpHermitePolynomial (n + 1) =
      hpHermitePolynomial (n + 1 + 1) +
        Polynomial.C (2 * (n : ℂ) + 2) *
          hpHermitePolynomial n := by
  rw [hpHermitePolynomial_succ (n + 1),
    hpHermitePolynomial_derivative_succ n]
  ring

theorem hpHermitePolynomial_three_term_eval
    (n : ℕ) (z : ℂ) :
    2 * z * (hpHermitePolynomial (n + 1)).eval z =
      (hpHermitePolynomial (n + 1 + 1)).eval z +
        (2 * (n : ℂ) + 2) *
          (hpHermitePolynomial n).eval z := by
  have h := congrArg
    (fun p : Polynomial ℂ => p.eval z)
    (hpHermitePolynomial_three_term n)
  simpa only [Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X] using h

#print axioms hpHermitePolynomial_three_term
#print axioms hpHermitePolynomial_three_term_eval

end HodgeProofHP
