import HodgeProofHP.Stage5ThetaJensenFoundations

/-!
# Quadratic Jensen polynomial and its moment discriminant

This module proves the degree-two formula and an algebraic equivalence
for the shift-zero discriminant. It does not assert that the discriminant
is nonnegative, prove real-rootedness, or establish an equivalence with RH.
The moment inequality remains a separate proof obligation.
-/

noncomputable section

namespace HodgeProofHP

theorem hpThetaJensenPolynomial_two (n : ℕ) :
    hpThetaJensenPolynomial 2 n =
      Polynomial.C (hpThetaJensenGamma n) +
        Polynomial.C (2 * hpThetaJensenGamma (n + 1)) * Polynomial.X +
        Polynomial.C (hpThetaJensenGamma (n + 2)) * Polynomial.X ^ 2 := by
  norm_num [hpThetaJensenPolynomial, Finset.sum_range_succ, Nat.choose, Polynomial.C_ofNat]

/-- The coefficient discriminant b² - 4ac of the quadratic formula above. -/
def hpThetaJensenQuadraticDiscriminant (n : ℕ) : ℝ :=
  (2 * hpThetaJensenGamma (n + 1)) ^ 2 -
    4 * hpThetaJensenGamma n * hpThetaJensenGamma (n + 2)

theorem hpThetaJensenQuadraticDiscriminant_zero :
    hpThetaJensenQuadraticDiscriminant 0 =
      hpThetaPhiEvenMoment 1 ^ 2 -
        hpThetaPhiEvenMoment 0 * hpThetaPhiMomentFour / 3 := by
  unfold hpThetaJensenQuadraticDiscriminant
  simp only [Nat.zero_add]
  rw [hpThetaJensenGamma_zero, hpThetaJensenGamma_one,
    hpThetaJensenGamma_two]
  ring

/-- This is an equivalence of conditions, not a proof of either condition. -/
theorem hpThetaJensenQuadraticDiscriminant_zero_nonneg_iff :
    0 ≤ hpThetaJensenQuadraticDiscriminant 0 ↔
      hpThetaPhiEvenMoment 0 * hpThetaPhiMomentFour ≤
        3 * hpThetaPhiEvenMoment 1 ^ 2 := by
  rw [hpThetaJensenQuadraticDiscriminant_zero]
  constructor <;> intro h <;> nlinarith

#print axioms hpThetaJensenPolynomial_two
#print axioms hpThetaJensenQuadraticDiscriminant_zero
#print axioms hpThetaJensenQuadraticDiscriminant_zero_nonneg_iff

end HodgeProofHP
