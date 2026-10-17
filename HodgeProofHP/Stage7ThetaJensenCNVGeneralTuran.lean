/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCNVScoreMoments
import HodgeProofHP.Stage5ThetaJensenCertifiedMomentInequality

/-!
# Strict Turan inequalities at every natural shift

The actual score comparison gives the strict normalized half-moment
inequality. The exact Gamma bridge transfers it to all positive Jensen
shifts. The previously certified numerical inequality supplies shift zero.
This does not assert hyperbolicity in unbounded Jensen degrees or RH.
-/
noncomputable section
namespace HodgeProofHP

theorem hpThetaCNVNormalizedHalfMoment_strict_inequality (n : ℕ) :
    hpThetaCNVNormalizedHalfMoment n * hpThetaCNVNormalizedHalfMoment (n + 2) <
      hpThetaCNVNormalizedHalfMoment (n + 1) ^ 2 := by
  have h := hpThetaCNVHalfMoment_strict_inequality n
  have ha : 0 < (n : ℝ) + 1 / 2 := by positivity
  have hb : 0 < (n : ℝ) + 3 / 2 := by positivity
  have hg : 0 < Real.Gamma ((n : ℝ) + 1 / 2) := Real.Gamma_pos_of_pos ha
  have hrec (k : ℕ) : Real.Gamma (((k + 1 : ℕ) : ℝ) + 1 / 2) =
      ((k : ℝ) + 1 / 2) * Real.Gamma ((k : ℝ) + 1 / 2) := by
    have he : ((k + 1 : ℕ) : ℝ) + 1 / 2 = ((k : ℝ) + 1 / 2) + 1 := by
      push_cast
      ring
    rw [he, Real.Gamma_add_one (by positivity : (k : ℝ) + 1 / 2 ≠ 0)]
  have hpos : 0 <
      (((n : ℝ) + 3 / 2) * hpThetaCNVHalfMoment (n + 1) ^ 2 -
        ((n : ℝ) + 1 / 2) * hpThetaCNVHalfMoment n * hpThetaCNVHalfMoment (n + 2)) /
      (((n : ℝ) + 1 / 2) ^ 2 * ((n : ℝ) + 3 / 2) *
        Real.Gamma ((n : ℝ) + 1 / 2) ^ 2) :=
    div_pos (sub_pos.mpr h) (by positivity)
  rw [← sub_pos]
  convert hpos using 1 <;>
    unfold hpThetaCNVNormalizedHalfMoment
  rw [show n + 2 = (n + 1) + 1 by omega, hrec (n + 1), hrec n]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [show (n : ℝ) + 1 + 1 / 2 = (n : ℝ) + 3 / 2 by ring]
  field_simp [ha.ne', hb.ne', hg.ne']
  <;> ring

theorem hpThetaJensen_strictTuran_positiveShift (n : ℕ) :
    hpThetaJensenGamma (n + 1) * hpThetaJensenGamma (n + 3) <
      hpThetaJensenGamma (n + 2) ^ 2 :=
  (hpThetaJensen_shiftedStrictTuran_iff_normalizedHalfMoments n).mpr
    (hpThetaCNVNormalizedHalfMoment_strict_inequality n)

theorem hpThetaJensen_strictTuran_zeroShift :
    hpThetaJensenGamma 0 * hpThetaJensenGamma 2 < hpThetaJensenGamma 1 ^ 2 := by
  apply (hpThetaJensen_strictTuran_iff_momentInequality 0).mpr
  have hzero : hpThetaPhiEvenMoment 0 = hpThetaPhiMomentZero := by
    simp [hpThetaPhiEvenMoment, hpThetaPhiMomentZero]
  have hone : hpThetaPhiEvenMoment 1 = hpThetaPhiMomentTwo := rfl
  norm_num only [Nat.cast_zero, zero_mul, zero_add, one_mul]
  rw [hzero, hone, hpThetaPhiEvenMoment_two]
  exact hpThetaJensen_moment_inequality_strict

theorem hpThetaJensen_strictTuran_allShifts (n : ℕ) :
    hpThetaJensenGamma n * hpThetaJensenGamma (n + 2) <
      hpThetaJensenGamma (n + 1) ^ 2 := by
  cases n with
  | zero => exact hpThetaJensen_strictTuran_zeroShift
  | succ n =>
    simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using
      hpThetaJensen_strictTuran_positiveShift n

#print axioms hpThetaCNVNormalizedHalfMoment_strict_inequality
#print axioms hpThetaJensen_strictTuran_positiveShift
#print axioms hpThetaJensen_strictTuran_zeroShift
#print axioms hpThetaJensen_strictTuran_allShifts
end HodgeProofHP
