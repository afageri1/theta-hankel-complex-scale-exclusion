import HodgeProofHP.Stage4ThetaPhiFourthIntegralDerivative
import Mathlib.Data.Polynomial.Basic
import Mathlib.Tactic

/-!
# Moment-based Jensen polynomial foundations

Define the even moments and the candidate Jensen coefficient sequence
gamma(n) = n! * M(2n) / (2n)!.

The intended analytic normalization is
Xi(i*z) = sum gamma(n) * z^(2*n) / n!.
The all-orders expansion is a subsequent proof obligation; it is not
asserted in this file. The factor Xi(0) can later be divided out.

This module does not prove hyperbolicity or an equivalence with RH.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace HodgeProofHP

/-- The even theta moment of order 2n. Integrability is proved separately. -/
def hpThetaPhiEvenMoment (n : ℕ) : ℝ :=
  ∫ u : ℝ in Set.Ioi 0,
    u ^ (2 * n) * hpRiemannThetaDifferentialKernel u

/-- Factorial normalization for the intended Jensen coefficient sequence. -/
def hpThetaJensenGamma (n : ℕ) : ℝ :=
  (Nat.factorial n : ℝ) * hpThetaPhiEvenMoment n /
    (Nat.factorial (2 * n) : ℝ)

/-- Degree d, shift n Jensen polynomial for the moment-based sequence. -/
def hpThetaJensenPolynomial (d n : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (d + 1),
    Polynomial.C ((Nat.choose d j : ℝ) * hpThetaJensenGamma (n + j)) *
      Polynomial.X ^ j

theorem hpThetaPhiEvenMoment_two :
    hpThetaPhiEvenMoment 2 = hpThetaPhiMomentFour := by
  rfl

theorem hpThetaJensenGamma_zero :
    hpThetaJensenGamma 0 = hpThetaPhiEvenMoment 0 := by
  norm_num [hpThetaJensenGamma, Nat.factorial]

theorem hpThetaJensenGamma_one :
    hpThetaJensenGamma 1 = hpThetaPhiEvenMoment 1 / 2 := by
  norm_num [hpThetaJensenGamma, Nat.factorial]

theorem hpThetaJensenGamma_two :
    hpThetaJensenGamma 2 = hpThetaPhiMomentFour / 12 := by
  rw [hpThetaJensenGamma, hpThetaPhiEvenMoment_two]
  norm_num [Nat.factorial]
  ring

theorem hpThetaJensenPolynomial_zero (n : ℕ) :
    hpThetaJensenPolynomial 0 n =
      Polynomial.C (hpThetaJensenGamma n) := by
  simp [hpThetaJensenPolynomial, Finset.sum_range_succ]

theorem hpThetaJensenPolynomial_one (n : ℕ) :
    hpThetaJensenPolynomial 1 n =
      Polynomial.C (hpThetaJensenGamma n) +
        Polynomial.C (hpThetaJensenGamma (n + 1)) * Polynomial.X := by
  simp [hpThetaJensenPolynomial, Finset.sum_range_succ]

#print axioms hpThetaPhiEvenMoment_two
#print axioms hpThetaJensenGamma_zero
#print axioms hpThetaJensenGamma_one
#print axioms hpThetaJensenGamma_two
#print axioms hpThetaJensenPolynomial_zero
#print axioms hpThetaJensenPolynomial_one

end HodgeProofHP
