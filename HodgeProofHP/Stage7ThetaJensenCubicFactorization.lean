/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCubicRealRoots
import HodgeProofHP.Stage7ThetaJensenSixthMomentCertifiedBounds
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.LinearCombination

/-! Exact real factorization and classification of all complex cubic zeros.
This is a degree-three certificate, not an unbounded-degree RH argument. -/
noncomputable section
namespace HodgeProofHP

theorem hpRealCubic_factor_of_three_roots
    (a b c d r1 r2 r3 : ℝ) (h12 : r1 < r2) (h23 : r2 < r3)
    (hz1 : a * r1 ^ 3 + b * r1 ^ 2 + c * r1 + d = 0)
    (hz2 : a * r2 ^ 3 + b * r2 ^ 2 + c * r2 + d = 0)
    (hz3 : a * r3 ^ 3 + b * r3 ^ 2 + c * r3 + d = 0) :
    ∀ x : ℝ, a * x ^ 3 + b * x ^ 2 + c * x + d =
      a * (x - r1) * (x - r2) * (x - r3) := by
  have hn12 : r1 - r2 ≠ 0 := sub_ne_zero.mpr (ne_of_lt h12)
  have hn23 : r2 - r3 ≠ 0 := sub_ne_zero.mpr (ne_of_lt h23)
  have hn13 : r1 - r3 ≠ 0 := sub_ne_zero.mpr (ne_of_lt (lt_trans h12 h23))
  have he12 : (r1 - r2) *
      (a * (r1 ^ 2 + r1 * r2 + r2 ^ 2) + b * (r1 + r2) + c) = 0 := by
    linear_combination hz1 - hz2
  have he23 : (r2 - r3) *
      (a * (r2 ^ 2 + r2 * r3 + r3 ^ 2) + b * (r2 + r3) + c) = 0 := by
    linear_combination hz2 - hz3
  have hl12 := (mul_eq_zero.mp he12).resolve_left hn12
  have hl23 := (mul_eq_zero.mp he23).resolve_left hn23
  have heb : (r1 - r3) * (a * (r1 + r2 + r3) + b) = 0 := by
    linear_combination hl12 - hl23
  have hb := (mul_eq_zero.mp heb).resolve_left hn13
  have hc : c - a * (r1 * r2 + r1 * r3 + r2 * r3) = 0 := by
    linear_combination hl12 - (r1 + r2) * hb
  have hd : d + a * r1 * r2 * r3 = 0 := by
    linear_combination hz1 - r1 ^ 2 * hb - r1 * hc
  intro x
  linear_combination x ^ 2 * hb + x * hc + hd

theorem hpThetaJensenGamma_three_pos : 0 < hpThetaJensenGamma 3 := by
  rw [hpThetaJensenGamma_three]
  have hm := hpThetaJensen_sixthMoment_ge_certified
  have hmpos : 0 < hpThetaPhiEvenMoment 3 := by linarith
  exact div_pos hmpos (by norm_num)

theorem hpThetaJensenCubic_exists_real_factorization :
    ∃ r1 r2 r3 : ℝ,
      r1 ∈ Set.Ioo (-90) (-55) ∧
      r2 ∈ Set.Ioo (-55) (-42) ∧
      r3 ∈ Set.Ioo (-42) (-15) ∧
      r1 < r2 ∧ r2 < r3 ∧
      hpThetaJensenPolynomial 3 0 =
        Polynomial.C (hpThetaJensenGamma 3) *
          (Polynomial.X - Polynomial.C r1) *
          (Polynomial.X - Polynomial.C r2) *
          (Polynomial.X - Polynomial.C r3) := by
  obtain ⟨r1, r2, r3, h1, h2, h3, h12, h23, hz1, hz2, hz3⟩ :=
    hpThetaJensenCubic_three_distinct_real_roots
  rw [hpThetaJensenCubic_eval] at hz1 hz2 hz3
  have hz1' : hpThetaJensenGamma 3 * r1 ^ 3 +
      (3 * hpThetaJensenGamma 2) * r1 ^ 2 +
      (3 * hpThetaJensenGamma 1) * r1 + hpThetaJensenGamma 0 = 0 := by
    nlinarith [hz1]
  have hz2' : hpThetaJensenGamma 3 * r2 ^ 3 +
      (3 * hpThetaJensenGamma 2) * r2 ^ 2 +
      (3 * hpThetaJensenGamma 1) * r2 + hpThetaJensenGamma 0 = 0 := by
    nlinarith [hz2]
  have hz3' : hpThetaJensenGamma 3 * r3 ^ 3 +
      (3 * hpThetaJensenGamma 2) * r3 ^ 2 +
      (3 * hpThetaJensenGamma 1) * r3 + hpThetaJensenGamma 0 = 0 := by
    nlinarith [hz3]
  have hf := hpRealCubic_factor_of_three_roots
    (hpThetaJensenGamma 3) (3 * hpThetaJensenGamma 2)
    (3 * hpThetaJensenGamma 1) (hpThetaJensenGamma 0)
    r1 r2 r3 h12 h23 hz1' hz2' hz3'
  refine ⟨r1, r2, r3, h1, h2, h3, h12, h23, ?_⟩
  apply Polynomial.funext
  intro x
  rw [hpThetaJensenCubic_eval]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_C, Polynomial.eval_X]
  calc
    _ = hpThetaJensenGamma 3 * x ^ 3 +
        (3 * hpThetaJensenGamma 2) * x ^ 2 +
        (3 * hpThetaJensenGamma 1) * x + hpThetaJensenGamma 0 := by ring
    _ = _ := hf x

theorem hpThetaJensenCubic_complex_zero_iff_of_factorization
    (r1 r2 r3 : ℝ)
    (hf : hpThetaJensenPolynomial 3 0 =
      Polynomial.C (hpThetaJensenGamma 3) *
        (Polynomial.X - Polynomial.C r1) *
        (Polynomial.X - Polynomial.C r2) *
        (Polynomial.X - Polynomial.C r3)) (w : ℂ) :
    (hpThetaJensenPolynomial 3 0).eval₂ Complex.ofRealHom w = 0 ↔
      w = (r1 : ℂ) ∨ w = (r2 : ℂ) ∨ w = (r3 : ℂ) := by
  have hg : (hpThetaJensenGamma 3 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hpThetaJensenGamma_three_pos)
  rw [hf]
  simp [Polynomial.eval₂_mul, hg, mul_eq_zero, sub_eq_zero, or_assoc]

theorem hpThetaJensenCubic_all_complex_zeros_real (w : ℂ)
    (hw : (hpThetaJensenPolynomial 3 0).eval₂ Complex.ofRealHom w = 0) :
    w.im = 0 := by
  obtain ⟨r1, r2, r3, h1, h2, h3, h12, h23, hf⟩ :=
    hpThetaJensenCubic_exists_real_factorization
  have hz := (hpThetaJensenCubic_complex_zero_iff_of_factorization r1 r2 r3 hf w).mp hw
  rcases hz with h | h | h <;> subst w <;> simp

#print axioms hpRealCubic_factor_of_three_roots
#print axioms hpThetaJensenGamma_three_pos
#print axioms hpThetaJensenCubic_exists_real_factorization
#print axioms hpThetaJensenCubic_complex_zero_iff_of_factorization
#print axioms hpThetaJensenCubic_all_complex_zeros_real
end HodgeProofHP
