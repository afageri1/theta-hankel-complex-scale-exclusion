/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoFiniteCoverage
import HodgeProofHP.Stage7ThetaJensenShiftTwoTailBounds
import HodgeProofHP.Stage7ThetaJensenDensityCubicBaseCase

/-!
# Certified shift-two cubic signs, distinct real roots and positive higher gap

The finite signed-integral certificates and the absolute tail bound give four
alternating signs. The intermediate value theorem supplies three ordered
roots. Their distinctness yields a positive discriminant and discharges the
weighted mixed-moment condition at p = 5/2. No assertion covers shifts n >= 3.
-/
noncomputable section
open MeasureTheory
namespace HodgeProofHP

theorem hpThetaJensenShiftTwo_eval_eq_finite_add_tail (p : ℝ) :
    (hpThetaJensenPolynomial 3 2).eval p =
      (∫ u : ℝ in Set.Ioo 0 1,
        hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight p u) +
      (∫ u : ℝ in Set.Ioi 1,
        hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight p u) := by
  simpa only [hpThetaJensenCubicShiftWeight_two] using
    hpThetaJensenCubicShift_eval_eq_finite_add_tail 2 p

theorem hpThetaJensenShiftTwo_eval_neg100_neg :
    (hpThetaJensenPolynomial 3 2).eval (-100) < 0 := by
  have hf := hpThetaShiftTwoNeg100_finiteIntegral_bounds.2
  have ht := abs_le.mp (hpThetaJensenShiftTwo_tail_abs_le (-100) (by norm_num))
  have hs := hpThetaJensenShiftTwo_eval_eq_finite_add_tail (-100)
  linarith only [hf, ht.2, hs]

theorem hpThetaJensenShiftTwo_eval_neg65_pos :
    0 < (hpThetaJensenPolynomial 3 2).eval (-65) := by
  have hf := hpThetaShiftTwoNeg65_finiteIntegral_bounds.1
  have ht := abs_le.mp (hpThetaJensenShiftTwo_tail_abs_le (-65) (by norm_num))
  have hs := hpThetaJensenShiftTwo_eval_eq_finite_add_tail (-65)
  linarith only [hf, ht.1, hs]

theorem hpThetaJensenShiftTwo_eval_neg45_neg :
    (hpThetaJensenPolynomial 3 2).eval (-45) < 0 := by
  have hf := hpThetaShiftTwoNeg45_finiteIntegral_bounds.2
  have ht := abs_le.mp (hpThetaJensenShiftTwo_tail_abs_le (-45) (by norm_num))
  have hs := hpThetaJensenShiftTwo_eval_eq_finite_add_tail (-45)
  linarith only [hf, ht.2, hs]

theorem hpThetaJensenShiftTwo_eval_neg25_pos :
    0 < (hpThetaJensenPolynomial 3 2).eval (-25) := by
  have hf := hpThetaShiftTwoNeg25_finiteIntegral_bounds.1
  have ht := abs_le.mp (hpThetaJensenShiftTwo_tail_abs_le (-25) (by norm_num))
  have hs := hpThetaJensenShiftTwo_eval_eq_finite_add_tail (-25)
  linarith only [hf, ht.1, hs]

theorem hpThetaJensenShiftTwo_three_distinct_real_roots :
    ∃ r1 r2 r3 : ℝ,
      r1 ∈ Set.Ioo (-100) (-65) ∧
      r2 ∈ Set.Ioo (-65) (-45) ∧
      r3 ∈ Set.Ioo (-45) (-25) ∧
      r1 < r2 ∧ r2 < r3 ∧
      (hpThetaJensenPolynomial 3 2).eval r1 = 0 ∧
      (hpThetaJensenPolynomial 3 2).eval r2 = 0 ∧
      (hpThetaJensenPolynomial 3 2).eval r3 = 0 := by
  obtain ⟨r1, h1, hz1⟩ := hpContinuous_exists_zero_Ioo_of_neg_pos
    (fun x => (hpThetaJensenPolynomial 3 2).eval x) (-100) (-65)
    (by norm_num) (hpThetaJensenPolynomial 3 2).continuous
    hpThetaJensenShiftTwo_eval_neg100_neg hpThetaJensenShiftTwo_eval_neg65_pos
  obtain ⟨r2, h2, hz2⟩ := hpContinuous_exists_zero_Ioo_of_pos_neg
    (fun x => (hpThetaJensenPolynomial 3 2).eval x) (-65) (-45)
    (by norm_num) (hpThetaJensenPolynomial 3 2).continuous
    hpThetaJensenShiftTwo_eval_neg65_pos hpThetaJensenShiftTwo_eval_neg45_neg
  obtain ⟨r3, h3, hz3⟩ := hpContinuous_exists_zero_Ioo_of_neg_pos
    (fun x => (hpThetaJensenPolynomial 3 2).eval x) (-45) (-25)
    (by norm_num) (hpThetaJensenPolynomial 3 2).continuous
    hpThetaJensenShiftTwo_eval_neg45_neg hpThetaJensenShiftTwo_eval_neg25_pos
  exact ⟨r1, r2, r3, h1, h2, h3, lt_trans h1.2 h2.1,
    lt_trans h2.2 h3.1, hz1, hz2, hz3⟩

private theorem hpShiftTwo_eval_coefficients (x : ℝ) :
    (hpThetaJensenPolynomial 3 2).eval x =
      hpThetaJensenGamma 5 * x ^ 3 + (3 * hpThetaJensenGamma 4) * x ^ 2 +
      (3 * hpThetaJensenGamma 3) * x + hpThetaJensenGamma 2 := by
  rw [hpThetaJensenPolynomial_three_allShifts]
  simp only [Nat.reduceAdd, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
  ring

theorem hpThetaJensenShiftTwo_discr_pos :
    0 < (hpThetaJensenShiftedCubic 2).discr := by
  obtain ⟨r1, r2, r3, h1, h2, h3, h12, h23, hz1, hz2, hz3⟩ :=
    hpThetaJensenShiftTwo_three_distinct_real_roots
  rw [hpShiftTwo_eval_coefficients] at hz1 hz2 hz3
  change 0 < (Cubic.mk (hpThetaJensenGamma 5) (3 * hpThetaJensenGamma 4)
    (3 * hpThetaJensenGamma 3) (hpThetaJensenGamma 2)).discr
  exact hpRealCubic_discr_pos_of_three_distinct_roots _ _ _ _ _ _ _
    (ne_of_gt (hpThetaJensenGamma_pos_allShifts 5)) h12 h23 hz1 hz2 hz3

theorem hpThetaJensenShiftTwo_higherTuranGap_pos :
    0 < hpThetaJensenHigherTuranGap 2 := by
  have h := hpThetaJensenShiftTwo_discr_pos
  rw [hpThetaJensenShiftedCubic_discr_eq_higherGap] at h
  nlinarith only [h]

theorem hpThetaDensityWeightedMixedGap_pos_fiveHalves :
    0 < hpThetaDensityWeightedMixedGap (5 / 2) := by
  have h := (hpThetaJensenHigherTuranGap_pos_iff_weightedMixedGap 2).mp
    hpThetaJensenShiftTwo_higherTuranGap_pos
  simpa only [hpThetaDensityJensenExponent, Nat.cast_ofNat,
    show (2 : ℝ) + 1 / 2 = 5 / 2 by norm_num] using h

theorem hpThetaJensenShiftTwo_all_complex_zeros_real (z : ℂ)
    (hz : (hpThetaJensenPolynomial 3 2).eval₂ Complex.ofRealHom z = 0) :
    z.im = 0 := by
  exact hpThetaJensenCubic_root_im_zero_of_higherGap 2
    hpThetaJensenShiftTwo_higherTuranGap_pos z hz

#print axioms hpThetaJensenShiftTwo_eval_eq_finite_add_tail
#print axioms hpThetaJensenShiftTwo_eval_neg100_neg
#print axioms hpThetaJensenShiftTwo_eval_neg65_pos
#print axioms hpThetaJensenShiftTwo_eval_neg45_neg
#print axioms hpThetaJensenShiftTwo_eval_neg25_pos
#print axioms hpThetaJensenShiftTwo_three_distinct_real_roots
#print axioms hpThetaJensenShiftTwo_discr_pos
#print axioms hpThetaJensenShiftTwo_higherTuranGap_pos
#print axioms hpThetaDensityWeightedMixedGap_pos_fiveHalves
#print axioms hpThetaJensenShiftTwo_all_complex_zeros_real
end HodgeProofHP
