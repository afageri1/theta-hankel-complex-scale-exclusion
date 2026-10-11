/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage5ThetaJensenFoundations
import Mathlib.Algebra.CubicDiscriminant

/-!
# Degree-three Jensen polynomial algebra

Expand J^(3,0) and identify its discriminant using Mathlib's Cubic.
No positivity certificate or real-root theorem is asserted here.
The sixth-moment bounds and discriminant positivity remain to be proved.
-/

noncomputable section

namespace HodgeProofHP

theorem hpThetaJensenGamma_three :
    hpThetaJensenGamma 3 = hpThetaPhiEvenMoment 3 / 120 := by
  norm_num [hpThetaJensenGamma, Nat.factorial] <;> ring

theorem hpThetaJensenPolynomial_three :
    hpThetaJensenPolynomial 3 0 =
      Polynomial.C (hpThetaJensenGamma 0) +
      Polynomial.C (3 * hpThetaJensenGamma 1) * Polynomial.X +
      Polynomial.C (3 * hpThetaJensenGamma 2) * Polynomial.X ^ 2 +
      Polynomial.C (hpThetaJensenGamma 3) * Polynomial.X ^ 3 := by
  norm_num [hpThetaJensenPolynomial, Finset.sum_range_succ, Nat.choose]

/-- The same polynomial in Mathlib's cubic representation. -/
def hpThetaJensenCubic : Cubic ℝ :=
  ⟨hpThetaJensenGamma 3, 3 * hpThetaJensenGamma 2,
    3 * hpThetaJensenGamma 1, hpThetaJensenGamma 0⟩

theorem hpThetaJensenCubic_toPoly :
    hpThetaJensenCubic.toPoly = hpThetaJensenPolynomial 3 0 := by
  rw [hpThetaJensenPolynomial_three]
  simp only [hpThetaJensenCubic, Cubic.toPoly]
  ring

theorem hpThetaJensenCubic_eval (x : ℝ) :
    (hpThetaJensenPolynomial 3 0).eval x =
      hpThetaJensenGamma 0 + 3 * hpThetaJensenGamma 1 * x +
      3 * hpThetaJensenGamma 2 * x ^ 2 + hpThetaJensenGamma 3 * x ^ 3 := by
  rw [hpThetaJensenPolynomial_three]
  simp

theorem hpThetaJensenCubic_eval_moments (x : ℝ) :
    (hpThetaJensenPolynomial 3 0).eval x =
      hpThetaPhiEvenMoment 0 + (3 / 2 : ℝ) * hpThetaPhiEvenMoment 1 * x +
      hpThetaPhiMomentFour / 4 * x ^ 2 + hpThetaPhiEvenMoment 3 / 120 * x ^ 3 := by
  rw [hpThetaJensenCubic_eval, hpThetaJensenGamma_zero, hpThetaJensenGamma_one,
    hpThetaJensenGamma_two, hpThetaJensenGamma_three]
  ring

theorem hpThetaJensenCubic_discr_moments :
    hpThetaJensenCubic.discr =
      (225 * hpThetaPhiMomentFour ^ 2 * hpThetaPhiEvenMoment 1 ^ 2 -
        180 * hpThetaPhiEvenMoment 3 * hpThetaPhiEvenMoment 1 ^ 3 -
        100 * hpThetaPhiMomentFour ^ 3 * hpThetaPhiEvenMoment 0 -
        3 * hpThetaPhiEvenMoment 3 ^ 2 * hpThetaPhiEvenMoment 0 ^ 2 +
        90 * hpThetaPhiEvenMoment 3 * hpThetaPhiMomentFour *
          hpThetaPhiEvenMoment 1 * hpThetaPhiEvenMoment 0) / 1600 := by
  simp only [Cubic.discr, hpThetaJensenCubic]
  rw [hpThetaJensenGamma_zero, hpThetaJensenGamma_one,
    hpThetaJensenGamma_two, hpThetaJensenGamma_three]
  ring

#print axioms hpThetaJensenGamma_three
#print axioms hpThetaJensenPolynomial_three
#print axioms hpThetaJensenCubic_toPoly
#print axioms hpThetaJensenCubic_eval
#print axioms hpThetaJensenCubic_eval_moments
#print axioms hpThetaJensenCubic_discr_moments

end HodgeProofHP
