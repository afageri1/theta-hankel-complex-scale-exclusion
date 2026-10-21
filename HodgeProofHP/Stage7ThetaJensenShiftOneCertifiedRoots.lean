/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneFiniteCoverage
import HodgeProofHP.Stage7ThetaJensenShiftOneTailBounds
import HodgeProofHP.Stage7ThetaJensenDensityCubicBaseCase

/-!
# Certified shift-one cubic signs, distinct real roots and positive higher gap

The finite signed-integral certificates and the absolute tail bound give four
alternating signs. The intermediate value theorem supplies three ordered
roots. Their distinctness yields a positive discriminant and discharges the
weighted mixed-moment condition at p = 3/2. No assertion covers shifts n >= 2.
-/
noncomputable section
namespace HodgeProofHP

theorem hpThetaJensenShiftOne_eval_neg100_neg :
    (hpThetaJensenPolynomial 3 1).eval (-100) < 0 := by
  have hf := hpThetaShiftOneNeg100_finiteIntegral_bounds.2
  have ht := abs_le.mp (hpThetaJensenShiftOne_tail_abs_le (-100) (by norm_num))
  have hs := hpThetaJensenShiftOne_eval_eq_finite_add_tail (-100)
  linarith only [hf, ht.2, hs]

theorem hpThetaJensenShiftOne_eval_neg65_pos :
    0 < (hpThetaJensenPolynomial 3 1).eval (-65) := by
  have hf := hpThetaShiftOneNeg65_finiteIntegral_bounds.1
  have ht := abs_le.mp (hpThetaJensenShiftOne_tail_abs_le (-65) (by norm_num))
  have hs := hpThetaJensenShiftOne_eval_eq_finite_add_tail (-65)
  linarith only [hf, ht.1, hs]

theorem hpThetaJensenShiftOne_eval_neg40_neg :
    (hpThetaJensenPolynomial 3 1).eval (-40) < 0 := by
  have hf := hpThetaShiftOneNeg40_finiteIntegral_bounds.2
  have ht := abs_le.mp (hpThetaJensenShiftOne_tail_abs_le (-40) (by norm_num))
  have hs := hpThetaJensenShiftOne_eval_eq_finite_add_tail (-40)
  linarith only [hf, ht.2, hs]

theorem hpThetaJensenShiftOne_eval_neg20_pos :
    0 < (hpThetaJensenPolynomial 3 1).eval (-20) := by
  have hf := hpThetaShiftOneNeg20_finiteIntegral_bounds.1
  have ht := abs_le.mp (hpThetaJensenShiftOne_tail_abs_le (-20) (by norm_num))
  have hs := hpThetaJensenShiftOne_eval_eq_finite_add_tail (-20)
  linarith only [hf, ht.1, hs]

theorem hpThetaJensenShiftOne_three_distinct_real_roots :
    ∃ r1 r2 r3 : ℝ,
      r1 ∈ Set.Ioo (-100) (-65) ∧
      r2 ∈ Set.Ioo (-65) (-40) ∧
      r3 ∈ Set.Ioo (-40) (-20) ∧
      r1 < r2 ∧ r2 < r3 ∧
      (hpThetaJensenPolynomial 3 1).eval r1 = 0 ∧
      (hpThetaJensenPolynomial 3 1).eval r2 = 0 ∧
      (hpThetaJensenPolynomial 3 1).eval r3 = 0 := by
  obtain ⟨r1, h1, hz1⟩ := hpContinuous_exists_zero_Ioo_of_neg_pos
    (fun x => (hpThetaJensenPolynomial 3 1).eval x) (-100) (-65)
    (by norm_num) (hpThetaJensenPolynomial 3 1).continuous
    hpThetaJensenShiftOne_eval_neg100_neg hpThetaJensenShiftOne_eval_neg65_pos
  obtain ⟨r2, h2, hz2⟩ := hpContinuous_exists_zero_Ioo_of_pos_neg
    (fun x => (hpThetaJensenPolynomial 3 1).eval x) (-65) (-40)
    (by norm_num) (hpThetaJensenPolynomial 3 1).continuous
    hpThetaJensenShiftOne_eval_neg65_pos hpThetaJensenShiftOne_eval_neg40_neg
  obtain ⟨r3, h3, hz3⟩ := hpContinuous_exists_zero_Ioo_of_neg_pos
    (fun x => (hpThetaJensenPolynomial 3 1).eval x) (-40) (-20)
    (by norm_num) (hpThetaJensenPolynomial 3 1).continuous
    hpThetaJensenShiftOne_eval_neg40_neg hpThetaJensenShiftOne_eval_neg20_pos
  exact ⟨r1, r2, r3, h1, h2, h3, lt_trans h1.2 h2.1,
    lt_trans h2.2 h3.1, hz1, hz2, hz3⟩

private theorem hpShiftOne_eval_coefficients (x : ℝ) :
    (hpThetaJensenPolynomial 3 1).eval x =
      hpThetaJensenGamma 4 * x ^ 3 + (3 * hpThetaJensenGamma 3) * x ^ 2 +
      (3 * hpThetaJensenGamma 2) * x + hpThetaJensenGamma 1 := by
  rw [hpThetaJensenPolynomial_three_allShifts]
  simp only [Nat.reduceAdd, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
  ring

theorem hpThetaJensenShiftOne_discr_pos :
    0 < (hpThetaJensenShiftedCubic 1).discr := by
  obtain ⟨r1, r2, r3, h1, h2, h3, h12, h23, hz1, hz2, hz3⟩ :=
    hpThetaJensenShiftOne_three_distinct_real_roots
  rw [hpShiftOne_eval_coefficients] at hz1 hz2 hz3
  change 0 < (Cubic.mk (hpThetaJensenGamma 4) (3 * hpThetaJensenGamma 3)
    (3 * hpThetaJensenGamma 2) (hpThetaJensenGamma 1)).discr
  exact hpRealCubic_discr_pos_of_three_distinct_roots _ _ _ _ _ _ _
    (ne_of_gt (hpThetaJensenGamma_pos_allShifts 4)) h12 h23 hz1 hz2 hz3

theorem hpThetaJensenShiftOne_higherTuranGap_pos :
    0 < hpThetaJensenHigherTuranGap 1 := by
  have h := hpThetaJensenShiftOne_discr_pos
  rw [hpThetaJensenShiftedCubic_discr_eq_higherGap] at h
  nlinarith only [h]

theorem hpThetaDensityWeightedMixedGap_pos_threeHalves :
    0 < hpThetaDensityWeightedMixedGap (3 / 2) := by
  have h := (hpThetaJensenHigherTuranGap_pos_iff_weightedMixedGap 1).mp
    hpThetaJensenShiftOne_higherTuranGap_pos
  simpa only [hpThetaDensityJensenExponent, Nat.cast_one,
    show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num] using h

theorem hpThetaJensenShiftOne_all_complex_zeros_real (z : ℂ)
    (hz : (hpThetaJensenPolynomial 3 1).eval₂ Complex.ofRealHom z = 0) :
    z.im = 0 := by
  exact hpThetaJensenCubic_root_im_zero_of_higherGap 1
    hpThetaJensenShiftOne_higherTuranGap_pos z hz

#print axioms hpThetaJensenShiftOne_eval_neg100_neg
#print axioms hpThetaJensenShiftOne_eval_neg65_pos
#print axioms hpThetaJensenShiftOne_eval_neg40_neg
#print axioms hpThetaJensenShiftOne_eval_neg20_pos
#print axioms hpThetaJensenShiftOne_three_distinct_real_roots
#print axioms hpThetaJensenShiftOne_discr_pos
#print axioms hpThetaJensenShiftOne_higherTuranGap_pos
#print axioms hpThetaDensityWeightedMixedGap_pos_threeHalves
#print axioms hpThetaJensenShiftOne_all_complex_zeros_real
end HodgeProofHP
