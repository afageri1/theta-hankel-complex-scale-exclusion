/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityCubicBridge
import HodgeProofHP.Stage7ThetaJensenCubicFactorization

/-!
# Unconditional weighted mixed-moment positivity at the first Jensen exponent

The previously certified three distinct roots at shift zero imply a positive
cubic discriminant. The exact density bridge then discharges the weighted
mixed-moment condition at p = 1/2. No positivity at a positive shift is assumed
or established here. The three-root certificate is reused, not reproved.
-/

noncomputable section
namespace HodgeProofHP

theorem hpRealCubic_discr_eq_root_separations (a r1 r2 r3 : ℝ) :
    (Cubic.mk a (-a * (r1 + r2 + r3))
      (a * (r1 * r2 + r1 * r3 + r2 * r3)) (-a * r1 * r2 * r3)).discr =
      a ^ 4 * (r1 - r2) ^ 2 * (r1 - r3) ^ 2 * (r2 - r3) ^ 2 := by
  simp only [Cubic.discr]
  ring

theorem hpRealCubic_discr_pos_of_three_distinct_roots
    (a b c d r1 r2 r3 : ℝ) (ha : a ≠ 0) (h12 : r1 < r2) (h23 : r2 < r3)
    (hz1 : a * r1 ^ 3 + b * r1 ^ 2 + c * r1 + d = 0)
    (hz2 : a * r2 ^ 3 + b * r2 ^ 2 + c * r2 + d = 0)
    (hz3 : a * r3 ^ 3 + b * r3 ^ 2 + c * r3 + d = 0) :
    0 < (Cubic.mk a b c d).discr := by
  have hf := hpRealCubic_factor_of_three_roots a b c d r1 r2 r3
    h12 h23 hz1 hz2 hz3
  have h0 := hf 0
  have h1 := hf 1
  have hm := hf (-1)
  have hb0 : b + a * (r1 + r2 + r3) = 0 := by
    linear_combination (1 / 2 : ℝ) * h1 + (1 / 2 : ℝ) * hm - h0
  have hc0 : c - a * (r1 * r2 + r1 * r3 + r2 * r3) = 0 := by
    linear_combination (1 / 2 : ℝ) * h1 - (1 / 2 : ℝ) * hm
  have hd0 : d + a * r1 * r2 * r3 = 0 := by
    linear_combination h0
  have hb : b = -a * (r1 + r2 + r3) := by linarith only [hb0]
  have hc : c = a * (r1 * r2 + r1 * r3 + r2 * r3) := by linarith only [hc0]
  have hd : d = -a * r1 * r2 * r3 := by linarith only [hd0]
  rw [hb, hc, hd, hpRealCubic_discr_eq_root_separations]
  have ha4 : 0 < a ^ 4 := by
    nlinarith only [sq_pos_of_ne_zero (pow_ne_zero 2 ha)]
  have hsq12 : 0 < (r1 - r2) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_lt h12))
  have hsq13 : 0 < (r1 - r3) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_lt (lt_trans h12 h23)))
  have hsq23 : 0 < (r2 - r3) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_lt h23))
  exact mul_pos (mul_pos (mul_pos ha4 hsq12) hsq13) hsq23

theorem hpThetaJensenCubic_discr_pos_zeroShift :
    0 < (hpThetaJensenShiftedCubic 0).discr := by
  obtain ⟨r1, r2, r3, h1, h2, h3, h12, h23, hz1, hz2, hz3⟩ :=
    hpThetaJensenCubic_three_distinct_real_roots
  rw [hpThetaJensenCubic_eval] at hz1 hz2 hz3
  have hz1' : hpThetaJensenGamma 3 * r1 ^ 3 +
      (3 * hpThetaJensenGamma 2) * r1 ^ 2 +
      (3 * hpThetaJensenGamma 1) * r1 + hpThetaJensenGamma 0 = 0 := by
    nlinarith only [hz1]
  have hz2' : hpThetaJensenGamma 3 * r2 ^ 3 +
      (3 * hpThetaJensenGamma 2) * r2 ^ 2 +
      (3 * hpThetaJensenGamma 1) * r2 + hpThetaJensenGamma 0 = 0 := by
    nlinarith only [hz2]
  have hz3' : hpThetaJensenGamma 3 * r3 ^ 3 +
      (3 * hpThetaJensenGamma 2) * r3 ^ 2 +
      (3 * hpThetaJensenGamma 1) * r3 + hpThetaJensenGamma 0 = 0 := by
    nlinarith only [hz3]
  change 0 < (Cubic.mk (hpThetaJensenGamma 3) (3 * hpThetaJensenGamma 2)
    (3 * hpThetaJensenGamma 1) (hpThetaJensenGamma 0)).discr
  exact hpRealCubic_discr_pos_of_three_distinct_roots _ _ _ _ _ _ _
    (ne_of_gt hpThetaJensenGamma_three_pos) h12 h23 hz1' hz2' hz3'

theorem hpThetaJensenHigherTuranGap_pos_zeroShift :
    0 < hpThetaJensenHigherTuranGap 0 := by
  have h := hpThetaJensenCubic_discr_pos_zeroShift
  rw [hpThetaJensenShiftedCubic_discr_eq_higherGap] at h
  nlinarith only [h]

theorem hpThetaDensityWeightedMixedGap_pos_half :
    0 < hpThetaDensityWeightedMixedGap (1 / 2) := by
  have h := (hpThetaJensenHigherTuranGap_pos_iff_weightedMixedGap 0).mp
    hpThetaJensenHigherTuranGap_pos_zeroShift
  simpa only [hpThetaDensityJensenExponent, Nat.cast_zero, zero_add] using h

theorem hpThetaDensityMixedMoment_weighted_determinant_pos_half :
    (3 / 2 : ℝ) * hpThetaDensityMixedMoment (3 / 2) (1 / 2) ^ 2 <
      (5 / 2 : ℝ) * hpThetaDensityMixedMoment (1 / 2) (1 / 2) *
        hpThetaDensityMixedMoment (3 / 2) (3 / 2) := by
  have h := hpThetaDensityWeightedMixedGap_pos_half
  simp only [hpThetaDensityWeightedMixedGap, show (1 / 2 : ℝ) + 1 = 3 / 2 by
    norm_num, show (1 / 2 : ℝ) + 2 = 5 / 2 by norm_num] at h
  exact sub_pos.mp h

#print axioms hpRealCubic_discr_eq_root_separations
#print axioms hpRealCubic_discr_pos_of_three_distinct_roots
#print axioms hpThetaJensenCubic_discr_pos_zeroShift
#print axioms hpThetaJensenHigherTuranGap_pos_zeroShift
#print axioms hpThetaDensityWeightedMixedGap_pos_half
#print axioms hpThetaDensityMixedMoment_weighted_determinant_pos_half
end HodgeProofHP
