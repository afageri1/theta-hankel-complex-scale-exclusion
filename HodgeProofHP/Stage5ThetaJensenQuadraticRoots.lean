import HodgeProofHP.Stage5ThetaJensenQuadratic
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Quadratic evaluation and the necessary real-root condition

We connect the polynomial to its coefficient discriminant by completing
the square. A real root implies a nonnegative discriminant, including
degenerate coefficient cases. We do not assert existence of a real root
or prove the theta moment inequality unconditionally.
-/

noncomputable section

namespace HodgeProofHP

theorem hpThetaJensenPolynomial_two_eval (n : ℕ) (x : ℝ) :
    (hpThetaJensenPolynomial 2 n).eval x =
      hpThetaJensenGamma n +
        (2 * hpThetaJensenGamma (n + 1)) * x +
        hpThetaJensenGamma (n + 2) * x ^ 2 := by
  rw [hpThetaJensenPolynomial_two]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow]

theorem hpThetaJensenQuadratic_complete_square (n : ℕ) (x : ℝ) :
    (2 * hpThetaJensenGamma (n + 2) * x +
        2 * hpThetaJensenGamma (n + 1)) ^ 2 =
      hpThetaJensenQuadraticDiscriminant n +
        4 * hpThetaJensenGamma (n + 2) *
          (hpThetaJensenPolynomial 2 n).eval x := by
  rw [hpThetaJensenPolynomial_two_eval]
  unfold hpThetaJensenQuadraticDiscriminant
  ring

theorem hpThetaJensenQuadraticDiscriminant_nonneg_of_real_root
    (n : ℕ) (x : ℝ)
    (hx : (hpThetaJensenPolynomial 2 n).eval x = 0) :
    0 ≤ hpThetaJensenQuadraticDiscriminant n := by
  have h := hpThetaJensenQuadratic_complete_square n x
  rw [hx, mul_zero, add_zero] at h
  rw [← h]
  exact sq_nonneg _

theorem hpThetaJensenQuadratic_moment_inequality_of_real_root
    (x : ℝ) (hx : (hpThetaJensenPolynomial 2 0).eval x = 0) :
    hpThetaPhiEvenMoment 0 * hpThetaPhiMomentFour ≤
      3 * hpThetaPhiEvenMoment 1 ^ 2 := by
  exact hpThetaJensenQuadraticDiscriminant_zero_nonneg_iff.mp
    (hpThetaJensenQuadraticDiscriminant_nonneg_of_real_root 0 x hx)

#print axioms hpThetaJensenPolynomial_two_eval
#print axioms hpThetaJensenQuadratic_complete_square
#print axioms hpThetaJensenQuadraticDiscriminant_nonneg_of_real_root
#print axioms hpThetaJensenQuadratic_moment_inequality_of_real_root

end HodgeProofHP
