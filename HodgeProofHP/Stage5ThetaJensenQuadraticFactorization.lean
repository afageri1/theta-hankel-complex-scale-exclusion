import HodgeProofHP.Stage5ThetaJensenCertifiedMomentInequality
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
# Two distinct real roots and real linear factorization at shift zero

The hypotheses of the generic quadratic factorization are discharged
by the certified theta moment inequality and fourth-moment positivity.
This file concerns only degree two and shift zero.
-/
noncomputable section
namespace HodgeProofHP

/-- The minus-sign quadratic-formula root. -/
def hpThetaJensenQuadraticRootMinus (n : ℕ) : ℝ :=
  (-2 * hpThetaJensenGamma (n + 1) -
      Real.sqrt (hpThetaJensenQuadraticDiscriminant n)) /
    (2 * hpThetaJensenGamma (n + 2))

theorem hpThetaJensenQuadratic_eval_factorization (n : ℕ)
    (ha : hpThetaJensenGamma (n + 2) ≠ 0)
    (hΔ : 0 ≤ hpThetaJensenQuadraticDiscriminant n) (x : ℝ) :
    (hpThetaJensenPolynomial 2 n).eval x =
      hpThetaJensenGamma (n + 2) *
        (x - hpThetaJensenQuadraticRootPlus n) *
        (x - hpThetaJensenQuadraticRootMinus n) := by
  have hid :
      (hpThetaJensenPolynomial 2 n).eval x -
        hpThetaJensenGamma (n + 2) *
          (x - hpThetaJensenQuadraticRootPlus n) *
          (x - hpThetaJensenQuadraticRootMinus n) =
      (Real.sqrt (hpThetaJensenQuadraticDiscriminant n) ^ 2 -
        hpThetaJensenQuadraticDiscriminant n) /
          (4 * hpThetaJensenGamma (n + 2)) := by
    rw [hpThetaJensenPolynomial_two_eval]
    unfold hpThetaJensenQuadraticRootPlus hpThetaJensenQuadraticRootMinus
      hpThetaJensenQuadraticDiscriminant
    (field_simp [ha]; ring)
  rw [Real.sq_sqrt hΔ, sub_self, zero_div] at hid
  exact sub_eq_zero.mp hid

theorem hpThetaJensenQuadratic_zero_eval_factorization (x : ℝ) :
    (hpThetaJensenPolynomial 2 0).eval x =
      hpThetaJensenGamma 2 * (x - hpThetaJensenQuadraticRootPlus 0) *
        (x - hpThetaJensenQuadraticRootMinus 0) := by
  simpa only [Nat.zero_add] using hpThetaJensenQuadratic_eval_factorization 0
    hpThetaJensenGamma_two_ne_zero
    (le_of_lt hpThetaJensenQuadratic_zero_discriminant_pos) x

theorem hpThetaJensenQuadratic_zero_rootMinus_certified :
    (hpThetaJensenPolynomial 2 0).eval (hpThetaJensenQuadraticRootMinus 0) = 0 := by
  rw [hpThetaJensenQuadratic_zero_eval_factorization]
  simp

theorem hpThetaJensenQuadratic_zero_rootMinus_lt_rootPlus :
    hpThetaJensenQuadraticRootMinus 0 < hpThetaJensenQuadraticRootPlus 0 := by
  have hs : 0 < Real.sqrt (hpThetaJensenQuadraticDiscriminant 0) :=
    Real.sqrt_pos.mpr hpThetaJensenQuadratic_zero_discriminant_pos
  have hd : 0 < 2 * hpThetaJensenGamma 2 :=
    mul_pos (by norm_num) hpThetaJensenGamma_two_pos
  have hdiff :
      hpThetaJensenQuadraticRootPlus 0 - hpThetaJensenQuadraticRootMinus 0 =
        (2 * Real.sqrt (hpThetaJensenQuadraticDiscriminant 0)) /
          (2 * hpThetaJensenGamma 2) := by
    unfold hpThetaJensenQuadraticRootPlus hpThetaJensenQuadraticRootMinus
    simp only [Nat.zero_add]
    ring
  apply sub_pos.mp
  rw [hdiff]
  exact div_pos (mul_pos (by norm_num) hs) hd

theorem hpThetaJensenQuadratic_zero_factorization :
    hpThetaJensenPolynomial 2 0 =
      Polynomial.C (hpThetaJensenGamma 2) *
        (Polynomial.X - Polynomial.C (hpThetaJensenQuadraticRootPlus 0)) *
        (Polynomial.X - Polynomial.C (hpThetaJensenQuadraticRootMinus 0)) := by
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_C, Polynomial.eval_X]
  exact hpThetaJensenQuadratic_zero_eval_factorization x

theorem hpThetaJensenQuadratic_zero_eval_eq_zero_iff (x : ℝ) :
    (hpThetaJensenPolynomial 2 0).eval x = 0 ↔
      x = hpThetaJensenQuadraticRootPlus 0 ∨
        x = hpThetaJensenQuadraticRootMinus 0 := by
  rw [hpThetaJensenQuadratic_zero_eval_factorization]
  simp [mul_eq_zero, hpThetaJensenGamma_two_ne_zero, sub_eq_zero]

theorem hpThetaJensenQuadratic_zero_two_distinct_real_roots :
    ∃ x y : ℝ, x < y ∧
      (hpThetaJensenPolynomial 2 0).eval x = 0 ∧
      (hpThetaJensenPolynomial 2 0).eval y = 0 :=
  ⟨hpThetaJensenQuadraticRootMinus 0, hpThetaJensenQuadraticRootPlus 0,
    hpThetaJensenQuadratic_zero_rootMinus_lt_rootPlus,
    hpThetaJensenQuadratic_zero_rootMinus_certified,
    hpThetaJensenQuadratic_zero_rootPlus_certified⟩

#print axioms hpThetaJensenQuadratic_eval_factorization
#print axioms hpThetaJensenQuadratic_zero_eval_factorization
#print axioms hpThetaJensenQuadratic_zero_rootMinus_certified
#print axioms hpThetaJensenQuadratic_zero_rootMinus_lt_rootPlus
#print axioms hpThetaJensenQuadratic_zero_factorization
#print axioms hpThetaJensenQuadratic_zero_eval_eq_zero_iff
#print axioms hpThetaJensenQuadratic_zero_two_distinct_real_roots
end HodgeProofHP
