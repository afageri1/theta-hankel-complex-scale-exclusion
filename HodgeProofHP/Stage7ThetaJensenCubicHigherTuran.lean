/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenQuadraticAllShifts
import HodgeProofHP.Stage7ThetaJensenCubicAlgebra

/-!
# Higher Turan gap for shifted cubic Jensen polynomials

Adjacent strict Turan gaps are positive at every shift. The cubic
discriminant is 27 times a higher gap involving four consecutive
coefficients. Its positivity is an additional obligation.

A rational counterexample shows that two adjacent strict Turan
inequalities alone do not imply positive cubic discriminant.
No cubic hyperbolicity at all shifts or unbounded good degrees is asserted.
-/

noncomputable section
namespace HodgeProofHP

def hpThetaJensenTuranGap (n : ℕ) : ℝ :=
  hpThetaJensenGamma (n + 1) ^ 2 -
    hpThetaJensenGamma n * hpThetaJensenGamma (n + 2)

def hpThetaJensenCrossGap (n : ℕ) : ℝ :=
  hpThetaJensenGamma (n + 1) * hpThetaJensenGamma (n + 2) -
    hpThetaJensenGamma n * hpThetaJensenGamma (n + 3)

def hpThetaJensenHigherTuranGap (n : ℕ) : ℝ :=
  4 * hpThetaJensenTuranGap n * hpThetaJensenTuranGap (n + 1) -
    hpThetaJensenCrossGap n ^ 2

def hpThetaJensenShiftedCubic (n : ℕ) : Cubic ℝ :=
  ⟨hpThetaJensenGamma (n + 3), 3 * hpThetaJensenGamma (n + 2),
    3 * hpThetaJensenGamma (n + 1), hpThetaJensenGamma n⟩

theorem hpThetaJensenPolynomial_three_allShifts (n : ℕ) :
    hpThetaJensenPolynomial 3 n =
      Polynomial.C (hpThetaJensenGamma n) +
      Polynomial.C (3 * hpThetaJensenGamma (n + 1)) * Polynomial.X +
      Polynomial.C (3 * hpThetaJensenGamma (n + 2)) * Polynomial.X ^ 2 +
      Polynomial.C (hpThetaJensenGamma (n + 3)) * Polynomial.X ^ 3 := by
  norm_num [hpThetaJensenPolynomial, Finset.sum_range_succ, Nat.choose]
  simp only [Polynomial.C_ofNat]

theorem hpThetaJensenShiftedCubic_toPoly (n : ℕ) :
    (hpThetaJensenShiftedCubic n).toPoly = hpThetaJensenPolynomial 3 n := by
  rw [hpThetaJensenPolynomial_three_allShifts]
  simp only [hpThetaJensenShiftedCubic, Cubic.toPoly]
  ring

theorem hpThetaJensenTuranGap_pos (n : ℕ) :
    0 < hpThetaJensenTuranGap n := by
  exact sub_pos.mpr (hpThetaJensen_strictTuran_allShifts n)

theorem hpThetaJensenCrossGap_balance (n : ℕ) :
    hpThetaJensenGamma (n + 1) * hpThetaJensenCrossGap n =
      hpThetaJensenGamma (n + 2) * hpThetaJensenTuranGap n +
      hpThetaJensenGamma n * hpThetaJensenTuranGap (n + 1) := by
  simp only [hpThetaJensenCrossGap, hpThetaJensenTuranGap, Nat.add_assoc]
  ring

theorem hpThetaJensenCrossGap_pos (n : ℕ) :
    0 < hpThetaJensenCrossGap n := by
  have h := add_pos
    (mul_pos (hpThetaJensenGamma_pos_allShifts (n + 2))
      (hpThetaJensenTuranGap_pos n))
    (mul_pos (hpThetaJensenGamma_pos_allShifts n)
      (hpThetaJensenTuranGap_pos (n + 1)))
  rw [← hpThetaJensenCrossGap_balance] at h
  by_contra hn
  have hm := mul_nonpos_of_nonneg_of_nonpos
    (hpThetaJensenGamma_pos_allShifts (n + 1)).le (le_of_not_gt hn)
  linarith

theorem hpThetaJensenShiftedCubic_discr_eq_higherGap (n : ℕ) :
    (hpThetaJensenShiftedCubic n).discr =
      27 * hpThetaJensenHigherTuranGap n := by
  simp only [Cubic.discr, hpThetaJensenShiftedCubic,
    hpThetaJensenHigherTuranGap, hpThetaJensenTuranGap,
    hpThetaJensenCrossGap, Nat.add_assoc]
  ring

theorem hpThetaJensenShiftedCubic_discr_pos_iff (n : ℕ) :
    0 < (hpThetaJensenShiftedCubic n).discr ↔
      hpThetaJensenCrossGap n ^ 2 <
        4 * hpThetaJensenTuranGap n * hpThetaJensenTuranGap (n + 1) := by
  rw [hpThetaJensenShiftedCubic_discr_eq_higherGap]
  unfold hpThetaJensenHigherTuranGap
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

theorem hpThetaJensenShiftedCubic_zero :
    hpThetaJensenShiftedCubic 0 = hpThetaJensenCubic := by
  rfl

/-- Adjacent strict Turan inequalities do not settle the cubic discriminant. -/
theorem hpThetaJensen_adjacentTuran_not_sufficient :
    ∃ a b c d : ℝ,
      0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
      a * c < b ^ 2 ∧ b * d < c ^ 2 ∧
      (Cubic.mk d (3 * c) (3 * b) a).discr < 0 := by
  refine ⟨9 / 10, 1, 1, 1 / 10, ?_⟩
  norm_num [Cubic.discr]

#print axioms hpThetaJensenPolynomial_three_allShifts
#print axioms hpThetaJensenShiftedCubic_toPoly
#print axioms hpThetaJensenTuranGap_pos
#print axioms hpThetaJensenCrossGap_balance
#print axioms hpThetaJensenCrossGap_pos
#print axioms hpThetaJensenShiftedCubic_discr_eq_higherGap
#print axioms hpThetaJensenShiftedCubic_discr_pos_iff
#print axioms hpThetaJensenShiftedCubic_zero
#print axioms hpThetaJensen_adjacentTuran_not_sufficient
end HodgeProofHP
