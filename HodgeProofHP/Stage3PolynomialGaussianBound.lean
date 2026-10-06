import HodgeProofHP.Stage3GaussianFirstDerivativeBound
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
A polynomial times a Gaussian remains bounded after multiplication
by any fixed polynomial weight.
-/

namespace HodgeProofHP

theorem hpPolynomialGaussian_weighted_bounded
    (p : Polynomial ℝ) (k : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ,
      |x| ^ k * |p.eval x| *
        Real.exp (-(1 / 2 : ℝ) * x ^ 2) ≤ C := by
  induction p using Polynomial.induction_on' generalizing k with
  | add p q hp hq =>
      obtain ⟨Cp, hp⟩ := hp k
      obtain ⟨Cq, hq⟩ := hq k
      refine ⟨Cp + Cq, fun x => ?_⟩
      have hle : |(p + q).eval x| ≤ |p.eval x| + |q.eval x| := by
        rw [Polynomial.eval_add]
        exact abs_add_le _ _
      have hfactor :
          0 ≤ |x| ^ k * Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
        positivity
      calc
        |x| ^ k * |(p + q).eval x| *
            Real.exp (-(1 / 2 : ℝ) * x ^ 2) =
          (|x| ^ k * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) *
            |(p + q).eval x| := by ring
        _ ≤ (|x| ^ k * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) *
              (|p.eval x| + |q.eval x|) :=
          mul_le_mul_of_nonneg_left hle hfactor
        _ =
          (|x| ^ k * |p.eval x| *
            Real.exp (-(1 / 2 : ℝ) * x ^ 2)) +
          (|x| ^ k * |q.eval x| *
            Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by ring
        _ ≤ Cp + Cq := add_le_add (hp x) (hq x)
  | monomial n a =>
      obtain ⟨C, hC⟩ := hpRealGaussian_weighted_bounded (k + n)
      refine ⟨|a| * C, fun x => ?_⟩
      calc
        |x| ^ k * |(Polynomial.monomial n a).eval x| *
            Real.exp (-(1 / 2 : ℝ) * x ^ 2) =
          |a| *
            (|x| ^ (k + n) *
              Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by
                rw [Polynomial.eval_monomial, abs_mul, abs_pow, pow_add]
                ring
        _ ≤ |a| * C :=
          mul_le_mul_of_nonneg_left (hC x) (abs_nonneg a)

#print axioms hpPolynomialGaussian_weighted_bounded

end HodgeProofHP
