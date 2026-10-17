/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCNVGeneralTuran
import HodgeProofHP.Stage5ThetaJensenQuadraticComplexRoots

/-!
# Two distinct negative real quadratic roots at every shift

The general strict Turan inequality makes every quadratic discriminant
positive. Positivity of the coefficients makes both real roots negative.
Mapping the real linear factorization to complex coefficients identifies
every complex zero with one of these two real roots.

The degree is fixed at two. This does not prove hyperbolicity in unbounded
degrees or the Riemann hypothesis.
-/
noncomputable section
namespace HodgeProofHP

theorem hpThetaJensenGamma_pos_allShifts (n : ℕ) : 0 < hpThetaJensenGamma n := by
  cases n with
  | zero => exact hpThetaJensenGamma_zero_pos
  | succ n =>
    rw [Nat.succ_eq_add_one, hpThetaJensenGamma_succ_eq_normalizedHalfMoment]
    exact mul_pos (div_pos (Real.Gamma_pos_of_pos (by norm_num)) (by positivity))
      (hpThetaCNVNormalizedHalfMoment_pos n)

theorem hpThetaJensenQuadratic_discriminant_pos_allShifts (n : ℕ) :
    0 < hpThetaJensenQuadraticDiscriminant n := by
  have h := hpThetaJensen_strictTuran_allShifts n
  unfold hpThetaJensenQuadraticDiscriminant
  nlinarith [h]

theorem hpThetaJensenQuadratic_eval_factorization_allShifts (n : ℕ) (x : ℝ) :
    (hpThetaJensenPolynomial 2 n).eval x =
      hpThetaJensenGamma (n + 2) *
        (x - hpThetaJensenQuadraticRootPlus n) *
        (x - hpThetaJensenQuadraticRootMinus n) :=
  hpThetaJensenQuadratic_eval_factorization n
    (hpThetaJensenGamma_pos_allShifts (n + 2)).ne'
    (hpThetaJensenQuadratic_discriminant_pos_allShifts n).le x

theorem hpThetaJensenQuadratic_rootMinus_lt_rootPlus_allShifts (n : ℕ) :
    hpThetaJensenQuadraticRootMinus n < hpThetaJensenQuadraticRootPlus n := by
  have hs : 0 < Real.sqrt (hpThetaJensenQuadraticDiscriminant n) :=
    Real.sqrt_pos.mpr (hpThetaJensenQuadratic_discriminant_pos_allShifts n)
  have hd : 0 < 2 * hpThetaJensenGamma (n + 2) :=
    mul_pos (by norm_num) (hpThetaJensenGamma_pos_allShifts (n + 2))
  have hdiff : hpThetaJensenQuadraticRootPlus n - hpThetaJensenQuadraticRootMinus n =
      (2 * Real.sqrt (hpThetaJensenQuadraticDiscriminant n)) /
        (2 * hpThetaJensenGamma (n + 2)) := by
    unfold hpThetaJensenQuadraticRootPlus hpThetaJensenQuadraticRootMinus
    ring
  apply sub_pos.mp
  rw [hdiff]
  exact div_pos (mul_pos (by norm_num) hs) hd

theorem hpThetaJensenQuadratic_factorization_allShifts (n : ℕ) :
    hpThetaJensenPolynomial 2 n =
      Polynomial.C (hpThetaJensenGamma (n + 2)) *
        (Polynomial.X - Polynomial.C (hpThetaJensenQuadraticRootPlus n)) *
        (Polynomial.X - Polynomial.C (hpThetaJensenQuadraticRootMinus n)) := by
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_C, Polynomial.eval_X]
  exact hpThetaJensenQuadratic_eval_factorization_allShifts n x

theorem hpThetaJensenQuadratic_two_distinct_real_roots_allShifts (n : ℕ) :
    ∃ x y : ℝ, x < y ∧ (hpThetaJensenPolynomial 2 n).eval x = 0 ∧
      (hpThetaJensenPolynomial 2 n).eval y = 0 := by
  refine ⟨hpThetaJensenQuadraticRootMinus n, hpThetaJensenQuadraticRootPlus n,
    hpThetaJensenQuadratic_rootMinus_lt_rootPlus_allShifts n, ?_, ?_⟩
  · rw [hpThetaJensenQuadratic_eval_factorization_allShifts]
    simp
  · rw [hpThetaJensenQuadratic_eval_factorization_allShifts]
    simp

theorem hpThetaJensenQuadratic_complex_factorization_allShifts (n : ℕ) :
    (hpThetaJensenPolynomial 2 n).map Complex.ofRealHom =
      Polynomial.C (hpThetaJensenGamma (n + 2) : ℂ) *
        (Polynomial.X - Polynomial.C (hpThetaJensenQuadraticRootPlus n : ℂ)) *
        (Polynomial.X - Polynomial.C (hpThetaJensenQuadraticRootMinus n : ℂ)) := by
  have h := congrArg (fun p : Polynomial ℝ => p.map Complex.ofRealHom)
    (hpThetaJensenQuadratic_factorization_allShifts n)
  simpa only [Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_C, Polynomial.map_X, Complex.ofRealHom_eq_coe] using h

theorem hpThetaJensenQuadratic_complex_eval_eq_zero_iff_allShifts (n : ℕ) (z : ℂ) :
    ((hpThetaJensenPolynomial 2 n).map Complex.ofRealHom).eval z = 0 ↔
      z = (hpThetaJensenQuadraticRootPlus n : ℂ) ∨
        z = (hpThetaJensenQuadraticRootMinus n : ℂ) := by
  have ha : (hpThetaJensenGamma (n + 2) : ℂ) ≠ 0 := by
    exact_mod_cast (hpThetaJensenGamma_pos_allShifts (n + 2)).ne'
  rw [hpThetaJensenQuadratic_complex_factorization_allShifts]
  simp [Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_C, Polynomial.eval_X, mul_eq_zero, ha, sub_eq_zero]

theorem hpThetaJensenQuadratic_complex_root_im_zero_allShifts (n : ℕ) (z : ℂ)
    (hz : ((hpThetaJensenPolynomial 2 n).map Complex.ofRealHom).eval z = 0) :
    z.im = 0 := by
  rcases (hpThetaJensenQuadratic_complex_eval_eq_zero_iff_allShifts n z).mp hz with h | h
  · rw [h]
    simp
  · rw [h]
    simp

theorem hpThetaJensenQuadratic_eval_pos_of_nonneg_allShifts (n : ℕ) (x : ℝ)
    (hx : 0 ≤ x) : 0 < (hpThetaJensenPolynomial 2 n).eval x := by
  rw [hpThetaJensenPolynomial_two_eval]
  have h0 := hpThetaJensenGamma_pos_allShifts n
  have h1 := hpThetaJensenGamma_pos_allShifts (n + 1)
  have h2 := hpThetaJensenGamma_pos_allShifts (n + 2)
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg h0 (mul_nonneg (by positivity) hx))
    (mul_nonneg h2.le (sq_nonneg x))

theorem hpThetaJensenQuadratic_real_root_neg_allShifts (n : ℕ) (x : ℝ)
    (hx : (hpThetaJensenPolynomial 2 n).eval x = 0) : x < 0 := by
  by_contra h
  have hp := hpThetaJensenQuadratic_eval_pos_of_nonneg_allShifts n x (le_of_not_gt h)
  rw [hx] at hp
  exact (lt_irrefl (0 : ℝ)) hp

theorem hpThetaJensenQuadratic_complex_root_negative_real_allShifts (n : ℕ) (z : ℂ)
    (hz : ((hpThetaJensenPolynomial 2 n).map Complex.ofRealHom).eval z = 0) :
    ∃ x : ℝ, x < 0 ∧ z = (x : ℂ) := by
  rcases (hpThetaJensenQuadratic_complex_eval_eq_zero_iff_allShifts n z).mp hz with h | h
  · refine ⟨hpThetaJensenQuadraticRootPlus n, ?_, h⟩
    apply hpThetaJensenQuadratic_real_root_neg_allShifts n
    rw [hpThetaJensenQuadratic_eval_factorization_allShifts]
    simp
  · refine ⟨hpThetaJensenQuadraticRootMinus n, ?_, h⟩
    apply hpThetaJensenQuadratic_real_root_neg_allShifts n
    rw [hpThetaJensenQuadratic_eval_factorization_allShifts]
    simp

#print axioms hpThetaJensenGamma_pos_allShifts
#print axioms hpThetaJensenQuadratic_discriminant_pos_allShifts
#print axioms hpThetaJensenQuadratic_eval_factorization_allShifts
#print axioms hpThetaJensenQuadratic_rootMinus_lt_rootPlus_allShifts
#print axioms hpThetaJensenQuadratic_factorization_allShifts
#print axioms hpThetaJensenQuadratic_two_distinct_real_roots_allShifts
#print axioms hpThetaJensenQuadratic_complex_factorization_allShifts
#print axioms hpThetaJensenQuadratic_complex_eval_eq_zero_iff_allShifts
#print axioms hpThetaJensenQuadratic_complex_root_im_zero_allShifts
#print axioms hpThetaJensenQuadratic_eval_pos_of_nonneg_allShifts
#print axioms hpThetaJensenQuadratic_real_root_neg_allShifts
#print axioms hpThetaJensenQuadratic_complex_root_negative_real_allShifts
end HodgeProofHP
