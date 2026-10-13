/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage5ThetaJensenFoundations

/-!
# Algebraic Turan-to-moment bridge

This file proves normalization identities and an equivalence only. It does not
prove the moment inequality for arbitrary shifts or an unbounded-degree result.
-/

noncomputable section
namespace HodgeProofHP

def hpThetaJensenMomentScale (n : ℕ) : ℝ :=
  (Nat.factorial n : ℝ) / (Nat.factorial (2 * n) : ℝ)

theorem hpThetaJensenMomentScale_pos (n : ℕ) :
    0 < hpThetaJensenMomentScale n := by
  unfold hpThetaJensenMomentScale
  exact div_pos (by exact_mod_cast Nat.factorial_pos n)
    (by exact_mod_cast Nat.factorial_pos (2 * n))

theorem hpThetaJensenGamma_succ_momentScale (n : ℕ) :
    hpThetaJensenGamma (n + 1) =
      hpThetaJensenMomentScale n * hpThetaPhiEvenMoment (n + 1) /
        (2 * (2 * (n : ℝ) + 1)) := by
  have hf : (Nat.factorial (2 * n) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * n)
  have ha : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  have hi : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
  unfold hpThetaJensenGamma hpThetaJensenMomentScale
  rw [hi]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  <;> first | ring | positivity

theorem hpThetaJensenGamma_add_two_momentScale (n : ℕ) :
    hpThetaJensenGamma (n + 2) =
      hpThetaJensenMomentScale n * hpThetaPhiEvenMoment (n + 2) /
        (4 * (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) := by
  have hf : (Nat.factorial (2 * n) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * n)
  have ha : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  have hb : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
  have hi : 2 * (n + 2) = (((2 * n + 1) + 1) + 1) + 1 := by omega
  have hn : n + 2 = (n + 1) + 1 := by omega
  unfold hpThetaJensenGamma hpThetaJensenMomentScale
  rw [hi, hn]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  <;> first | ring | positivity

def hpThetaJensenTuranMomentScale (n : ℕ) : ℝ :=
  hpThetaJensenMomentScale n ^ 2 /
    (4 * (2 * (n : ℝ) + 1) ^ 2 * (2 * (n : ℝ) + 3))

theorem hpThetaJensenTuranMomentScale_pos (n : ℕ) :
    0 < hpThetaJensenTuranMomentScale n := by
  have hs := hpThetaJensenMomentScale_pos n
  unfold hpThetaJensenTuranMomentScale
  positivity

theorem hpThetaJensen_turanGap_eq_momentGap (n : ℕ) :
    hpThetaJensenGamma (n + 1) ^ 2 -
        hpThetaJensenGamma n * hpThetaJensenGamma (n + 2) =
      hpThetaJensenTuranMomentScale n *
        ((2 * (n : ℝ) + 3) * hpThetaPhiEvenMoment (n + 1) ^ 2 -
          (2 * (n : ℝ) + 1) *
            hpThetaPhiEvenMoment n * hpThetaPhiEvenMoment (n + 2)) := by
  have ha : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  have hb : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
  have hzero : hpThetaJensenGamma n =
      hpThetaJensenMomentScale n * hpThetaPhiEvenMoment n := by
    unfold hpThetaJensenGamma hpThetaJensenMomentScale
    ring
  rw [hpThetaJensenGamma_succ_momentScale,
    hpThetaJensenGamma_add_two_momentScale, hzero]
  unfold hpThetaJensenTuranMomentScale
  field_simp
  <;> first | ring | positivity

theorem hpThetaJensen_strictTuran_iff_momentInequality (n : ℕ) :
    hpThetaJensenGamma n * hpThetaJensenGamma (n + 2) <
        hpThetaJensenGamma (n + 1) ^ 2 ↔
      (2 * (n : ℝ) + 1) *
          hpThetaPhiEvenMoment n * hpThetaPhiEvenMoment (n + 2) <
        (2 * (n : ℝ) + 3) * hpThetaPhiEvenMoment (n + 1) ^ 2 := by
  rw [← sub_pos, hpThetaJensen_turanGap_eq_momentGap]
  exact (mul_pos_iff_of_pos_left (hpThetaJensenTuranMomentScale_pos n)).trans
    sub_pos

#print axioms hpThetaJensenMomentScale_pos
#print axioms hpThetaJensenGamma_succ_momentScale
#print axioms hpThetaJensenGamma_add_two_momentScale
#print axioms hpThetaJensenTuranMomentScale_pos
#print axioms hpThetaJensen_turanGap_eq_momentGap
#print axioms hpThetaJensen_strictTuran_iff_momentInequality

end HodgeProofHP
