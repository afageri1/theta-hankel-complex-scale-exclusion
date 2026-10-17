/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCubicHigherTuran

/-!
# Conditional cubic real zeros from the higher Turan gap

A nonreal zero forces the real cubic discriminant to be nonpositive.
Consequently a positive higher Turan gap implies that every complex zero
of the corresponding shifted Jensen cubic is real. Real zeros are negative
because all four coefficients are positive.

The higher-gap hypothesis is explicit and is not discharged here.
This module does not prove cubic hyperbolicity at every shift unconditionally,
hyperbolicity in unbounded degrees, or RH.
-/

noncomputable section
namespace HodgeProofHP

theorem hpRealCubic_root_im_zero_of_discr_pos
    (a b c d : ℝ) (z : ℂ)
    (hdisc : 0 < (Cubic.mk a b c d).discr)
    (hz : (a : ℂ) * z ^ 3 + (b : ℂ) * z ^ 2 + (c : ℂ) * z + (d : ℂ) = 0) :
    z.im = 0 := by
  by_contra hy
  have hr := congrArg Complex.re hz
  have hi := congrArg Complex.im hz
  norm_num [pow_succ, Complex.mul_re, Complex.mul_im] at hr hi
  have hf : z.im *
      (a * (3 * z.re ^ 2 - z.im ^ 2) + 2 * b * z.re + c) = 0 := by
    nlinarith [hi]
  have hc : c = a * (z.im ^ 2 - 3 * z.re ^ 2) - 2 * b * z.re := by
    have h := (mul_eq_zero.mp hf).resolve_left hy
    nlinarith [h]
  have hd : d = (z.re ^ 2 + z.im ^ 2) * (2 * a * z.re + b) := by
    rw [hc] at hr
    nlinarith [hr]
  have he : (Cubic.mk a b c d).discr =
      -4 * z.im ^ 2 * ((3 * a * z.re + b) ^ 2 + a ^ 2 * z.im ^ 2) ^ 2 := by
    simp only [Cubic.discr]
    rw [hc, hd]
    ring
  have hn : 0 ≤
      4 * z.im ^ 2 * ((3 * a * z.re + b) ^ 2 + a ^ 2 * z.im ^ 2) ^ 2 := by
    positivity
  rw [he] at hdisc
  nlinarith only [hdisc, hn]

theorem hpThetaJensenCubic_evalComplex_allShifts (n : ℕ) (z : ℂ) :
    (hpThetaJensenPolynomial 3 n).eval₂ Complex.ofRealHom z =
      (hpThetaJensenGamma (n + 3) : ℂ) * z ^ 3 +
      ((3 * hpThetaJensenGamma (n + 2) : ℝ) : ℂ) * z ^ 2 +
      ((3 * hpThetaJensenGamma (n + 1) : ℝ) : ℂ) * z +
      (hpThetaJensenGamma n : ℂ) := by
  rw [hpThetaJensenPolynomial_three_allShifts]
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_pow,
    Complex.ofRealHom_eq_coe]
  ring

theorem hpThetaJensenCubic_root_im_zero_of_higherGap
    (n : ℕ) (hgap : 0 < hpThetaJensenHigherTuranGap n) (z : ℂ)
    (hz : (hpThetaJensenPolynomial 3 n).eval₂ Complex.ofRealHom z = 0) :
    z.im = 0 := by
  have hd : 0 < (hpThetaJensenShiftedCubic n).discr := by
    rw [hpThetaJensenShiftedCubic_discr_eq_higherGap]
    exact mul_pos (by norm_num) hgap
  rw [hpThetaJensenCubic_evalComplex_allShifts] at hz
  exact hpRealCubic_root_im_zero_of_discr_pos
    (hpThetaJensenGamma (n + 3)) (3 * hpThetaJensenGamma (n + 2))
    (3 * hpThetaJensenGamma (n + 1)) (hpThetaJensenGamma n) z hd hz

theorem hpThetaJensenCubic_eval_pos_of_nonneg_allShifts
    (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 < (hpThetaJensenPolynomial 3 n).eval x := by
  have h0 := hpThetaJensenGamma_pos_allShifts n
  have h1 := hpThetaJensenGamma_pos_allShifts (n + 1)
  have h2 := hpThetaJensenGamma_pos_allShifts (n + 2)
  have h3 := hpThetaJensenGamma_pos_allShifts (n + 3)
  rw [hpThetaJensenPolynomial_three_allShifts]
  simp only [Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
  positivity

theorem hpThetaJensenCubic_real_root_neg_allShifts
    (n : ℕ) (x : ℝ) (hx : (hpThetaJensenPolynomial 3 n).eval x = 0) :
    x < 0 := by
  by_contra hn
  have hp := hpThetaJensenCubic_eval_pos_of_nonneg_allShifts n x (le_of_not_gt hn)
  rw [hx] at hp
  exact (lt_irrefl (0 : ℝ)) hp

theorem hpThetaJensenCubic_allShifts_realZeros_of_higherGaps
    (hgap : ∀ n : ℕ, 0 < hpThetaJensenHigherTuranGap n) :
    ∀ (n : ℕ) (z : ℂ),
      (hpThetaJensenPolynomial 3 n).eval₂ Complex.ofRealHom z = 0 → z.im = 0 := by
  intro n z hz
  exact hpThetaJensenCubic_root_im_zero_of_higherGap n (hgap n) z hz

#print axioms hpRealCubic_root_im_zero_of_discr_pos
#print axioms hpThetaJensenCubic_evalComplex_allShifts
#print axioms hpThetaJensenCubic_root_im_zero_of_higherGap
#print axioms hpThetaJensenCubic_eval_pos_of_nonneg_allShifts
#print axioms hpThetaJensenCubic_real_root_neg_allShifts
#print axioms hpThetaJensenCubic_allShifts_realZeros_of_higherGaps
end HodgeProofHP
