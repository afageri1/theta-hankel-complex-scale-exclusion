/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCNVTailMomentIdentity
import HodgeProofHP.Stage7ThetaJensenTuranMomentEquivalence

/-!
# Gamma normalization and the exact shifted Turan gap

The half-integer moment J(n) of the actual square tail is normalized as
L(n) = J(n) / Gamma(n+1/2). Its relation to the Jensen coefficients is
gamma(n+1) = Gamma(1/2) / (2 * 4^(n+1)) * L(n).

The geometric factor cancels in the strict Turan comparison. This file proves
the resulting equivalence at shifts n+1; it does not prove log concavity of
L, general Turan inequalities, or unbounded good Jensen degrees.
-/
noncomputable section
open MeasureTheory Filter
namespace HodgeProofHP

def hpThetaCNVHalfMoment (n : ℕ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), x ^ ((n : ℝ) - 1 / 2) * hpThetaPhiSquareTail x

def hpThetaCNVNormalizedHalfMoment (n : ℕ) : ℝ :=
  hpThetaCNVHalfMoment n / Real.Gamma ((n : ℝ) + 1 / 2)

theorem hpThetaCNV_halfGamma_factorial_balance (n : ℕ) :
    Real.Gamma ((n : ℝ) + 1 / 2) * (4 : ℝ) ^ n * (Nat.factorial n : ℝ) =
      (Nat.factorial (2 * n) : ℝ) * Real.Gamma (1 / 2) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have harg : ((n + 1 : ℕ) : ℝ) + 1 / 2 = ((n : ℝ) + 1 / 2) + 1 := by
      push_cast
      ring
    have hindex : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    rw [harg, Real.Gamma_add_one (by positivity : (n : ℝ) + 1 / 2 ≠ 0), hindex]
    simp only [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    calc
      _ = (4 * ((n : ℝ) + 1) * ((n : ℝ) + 1 / 2)) *
          (Real.Gamma ((n : ℝ) + 1 / 2) * 4 ^ n * (Nat.factorial n : ℝ)) := by ring
      _ = _ := by rw [ih]; ring

theorem hpThetaCNV_halfGamma_factorial_ratio (n : ℕ) :
    Real.Gamma (1 / 2) / ((4 : ℝ) ^ n * Real.Gamma ((n : ℝ) + 1 / 2)) =
      (Nat.factorial n : ℝ) / (Nat.factorial (2 * n) : ℝ) := by
  have hg : 0 < Real.Gamma ((n : ℝ) + 1 / 2) :=
    Real.Gamma_pos_of_pos (by positivity)
  have hf : (Nat.factorial (2 * n) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * n)
  apply (div_eq_div_iff (by positivity) hf).mpr
  nlinarith [hpThetaCNV_halfGamma_factorial_balance n]

theorem hpThetaCNVHalfMoment_eq_evenMoment (n : ℕ) :
    hpThetaCNVHalfMoment n =
      4 / (2 * (n : ℝ) + 1) * hpThetaPhiEvenMoment (n + 1) :=
  hpThetaPhiSquareTail_halfMoment_eq_evenMoment n

theorem hpThetaCNVHalfMoment_pos (n : ℕ) : 0 < hpThetaCNVHalfMoment n := by
  have hs : (Function.support (fun x : ℝ =>
      x ^ ((n : ℝ) - 1 / 2) * hpThetaPhiSquareTail x)) ∩ Set.Ioi 0 = Set.Ioi 0 := by
    rw [Set.inter_eq_right]
    intro x hx
    rw [Function.mem_support]
    exact (mul_pos (Real.rpow_pos_of_pos hx _) (hpThetaPhiSquareTail_pos x hx)).ne'
  unfold hpThetaCNVHalfMoment
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · rw [hs, Real.volume_Ioi, ← ENNReal.ofReal_zero]
    exact ENNReal.ofReal_lt_top
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (mul_pos (Real.rpow_pos_of_pos hx _) (hpThetaPhiSquareTail_pos x hx)).le
  · exact hpThetaPhiSquareTail_halfMoment_integrableOn n

theorem hpThetaCNVNormalizedHalfMoment_pos (n : ℕ) :
    0 < hpThetaCNVNormalizedHalfMoment n := by
  exact div_pos (hpThetaCNVHalfMoment_pos n) (Real.Gamma_pos_of_pos (by positivity))

theorem hpThetaJensenGamma_succ_eq_normalizedHalfMoment (n : ℕ) :
    hpThetaJensenGamma (n + 1) =
      Real.Gamma (1 / 2) / (2 * (4 : ℝ) ^ (n + 1)) *
        hpThetaCNVNormalizedHalfMoment n := by
  have hg : Real.Gamma ((n : ℝ) + 1 / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hfour : (4 : ℝ) ^ n ≠ 0 := by positivity
  have hindex : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  rw [hpThetaJensenGamma_succ_momentScale]
  unfold hpThetaJensenMomentScale hpThetaCNVNormalizedHalfMoment
  rw [hpThetaCNVHalfMoment_eq_evenMoment, ← hpThetaCNV_halfGamma_factorial_ratio n]
  rw [pow_succ]
  field_simp
  <;> ring

theorem hpThetaJensen_shiftedTuranGap_eq_normalizedHalfMomentGap (n : ℕ) :
    hpThetaJensenGamma (n + 2) ^ 2 -
        hpThetaJensenGamma (n + 1) * hpThetaJensenGamma (n + 3) =
      (Real.Gamma (1 / 2) / (2 * (4 : ℝ) ^ (n + 2))) ^ 2 *
        (hpThetaCNVNormalizedHalfMoment (n + 1) ^ 2 -
          hpThetaCNVNormalizedHalfMoment n * hpThetaCNVNormalizedHalfMoment (n + 2)) := by
  have hfour : (4 : ℝ) ^ n ≠ 0 := by positivity
  have htwo : n + 2 = (n + 1) + 1 := by omega
  have hthree : n + 3 = (n + 2) + 1 := by omega
  rw [hthree, hpThetaJensenGamma_succ_eq_normalizedHalfMoment (n + 2)]
  rw [htwo, hpThetaJensenGamma_succ_eq_normalizedHalfMoment (n + 1),
    hpThetaJensenGamma_succ_eq_normalizedHalfMoment n]
  simp only [pow_succ, pow_zero]
  field_simp
  <;> ring

theorem hpThetaJensen_shiftedStrictTuran_iff_normalizedHalfMoments (n : ℕ) :
    hpThetaJensenGamma (n + 1) * hpThetaJensenGamma (n + 3) <
        hpThetaJensenGamma (n + 2) ^ 2 ↔
      hpThetaCNVNormalizedHalfMoment n * hpThetaCNVNormalizedHalfMoment (n + 2) <
        hpThetaCNVNormalizedHalfMoment (n + 1) ^ 2 := by
  have hg : 0 < Real.Gamma (1 / 2) := Real.Gamma_pos_of_pos (by norm_num)
  have hc : 0 < (Real.Gamma (1 / 2) / (2 * (4 : ℝ) ^ (n + 2))) ^ 2 := by
    positivity
  rw [← sub_pos, hpThetaJensen_shiftedTuranGap_eq_normalizedHalfMomentGap]
  exact (mul_pos_iff_of_pos_left hc).trans sub_pos

#print axioms hpThetaCNV_halfGamma_factorial_balance
#print axioms hpThetaCNV_halfGamma_factorial_ratio
#print axioms hpThetaCNVHalfMoment_eq_evenMoment
#print axioms hpThetaCNVHalfMoment_pos
#print axioms hpThetaCNVNormalizedHalfMoment_pos
#print axioms hpThetaJensenGamma_succ_eq_normalizedHalfMoment
#print axioms hpThetaJensen_shiftedTuranGap_eq_normalizedHalfMomentGap
#print axioms hpThetaJensen_shiftedStrictTuran_iff_normalizedHalfMoments
end HodgeProofHP
