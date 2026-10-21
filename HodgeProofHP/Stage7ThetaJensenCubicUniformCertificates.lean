/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCubicAllShiftTailBounds
import HodgeProofHP.Stage7ThetaJensenCubicSharpDefectCriterion

/-!
# Uniform cubic certification from four signed finite integrals

The analytic tail estimate is combined with four explicit finite-integral
margins. Such a certificate yields three distinct real roots, a positive
discriminant, a positive higher gap, and the exact sharp defect step.

No new finite-integral margin or certificate at shifts n >= 3 is assumed
without an explicit theorem argument. This module does not establish
unconditional all-shift cubic hyperbolicity.
-/
noncomputable section
open MeasureTheory
namespace HodgeProofHP

def hpThetaJensenCubicCutoffIntegral (n : ℕ) (p R : ℝ) : ℝ :=
  ∫ u : ℝ in Set.Ioo 0 R,
    hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicShiftWeight n p u

structure hpThetaJensenCubicSignCertificate (n : ℕ) where
  x0 : ℝ
  x1 : ℝ
  x2 : ℝ
  x3 : ℝ
  ordered01 : x0 < x1
  ordered12 : x1 < x2
  ordered23 : x2 < x3
  neg0 : (hpThetaJensenPolynomial 3 n).eval x0 < 0
  pos1 : 0 < (hpThetaJensenPolynomial 3 n).eval x1
  neg2 : (hpThetaJensenPolynomial 3 n).eval x2 < 0
  pos3 : 0 < (hpThetaJensenPolynomial 3 n).eval x3

theorem hpThetaJensenCubic_signs_of_cutoff_margins
    (n : ℕ) (R x0 x1 x2 x3 : ℝ) (hR : hpThetaJensenCubicTailCutoff n ≤ R)
    (h0 : hpThetaJensenCubicCutoffIntegral n x0 R +
      hpThetaJensenCubicShiftTailUpper n x0 R < 0)
    (h1 : hpThetaJensenCubicShiftTailUpper n x1 R <
      hpThetaJensenCubicCutoffIntegral n x1 R)
    (h2 : hpThetaJensenCubicCutoffIntegral n x2 R +
      hpThetaJensenCubicShiftTailUpper n x2 R < 0)
    (h3 : hpThetaJensenCubicShiftTailUpper n x3 R <
      hpThetaJensenCubicCutoffIntegral n x3 R) :
    (hpThetaJensenPolynomial 3 n).eval x0 < 0 ∧
      0 < (hpThetaJensenPolynomial 3 n).eval x1 ∧
      (hpThetaJensenPolynomial 3 n).eval x2 < 0 ∧
      0 < (hpThetaJensenPolynomial 3 n).eval x3 := by
  have he (p : ℝ) :
      |(hpThetaJensenPolynomial 3 n).eval p - hpThetaJensenCubicCutoffIntegral n p R| ≤
        hpThetaJensenCubicShiftTailUpper n p R :=
    hpThetaJensenCubicShift_eval_error_le n p R hR
  have he0 := (abs_le.mp (he x0)).2
  have he1 := (abs_le.mp (he x1)).1
  have he2 := (abs_le.mp (he x2)).2
  have he3 := (abs_le.mp (he x3)).1
  exact ⟨by linarith only [he0, h0], by linarith only [he1, h1],
    by linarith only [he2, h2], by linarith only [he3, h3]⟩

theorem hpThetaJensenCubic_signCertificate_of_cutoff_margins
    (n : ℕ) (R x0 x1 x2 x3 : ℝ) (hR : hpThetaJensenCubicTailCutoff n ≤ R)
    (h01 : x0 < x1) (h12 : x1 < x2) (h23 : x2 < x3)
    (h0 : hpThetaJensenCubicCutoffIntegral n x0 R +
      hpThetaJensenCubicShiftTailUpper n x0 R < 0)
    (h1 : hpThetaJensenCubicShiftTailUpper n x1 R <
      hpThetaJensenCubicCutoffIntegral n x1 R)
    (h2 : hpThetaJensenCubicCutoffIntegral n x2 R +
      hpThetaJensenCubicShiftTailUpper n x2 R < 0)
    (h3 : hpThetaJensenCubicShiftTailUpper n x3 R <
      hpThetaJensenCubicCutoffIntegral n x3 R) :
    Nonempty (hpThetaJensenCubicSignCertificate n) := by
  obtain ⟨hs0, hs1, hs2, hs3⟩ :=
    hpThetaJensenCubic_signs_of_cutoff_margins n R x0 x1 x2 x3 hR h0 h1 h2 h3
  exact ⟨⟨x0, x1, x2, x3, h01, h12, h23, hs0, hs1, hs2, hs3⟩⟩

theorem hpThetaJensenCubic_three_distinct_roots_of_signCertificate
    (n : ℕ) (c : hpThetaJensenCubicSignCertificate n) :
    ∃ r1 r2 r3 : ℝ,
      r1 ∈ Set.Ioo c.x0 c.x1 ∧ r2 ∈ Set.Ioo c.x1 c.x2 ∧
      r3 ∈ Set.Ioo c.x2 c.x3 ∧ r1 < r2 ∧ r2 < r3 ∧ r3 < 0 ∧
      (hpThetaJensenPolynomial 3 n).eval r1 = 0 ∧
      (hpThetaJensenPolynomial 3 n).eval r2 = 0 ∧
      (hpThetaJensenPolynomial 3 n).eval r3 = 0 := by
  obtain ⟨r1, h1, hz1⟩ := hpContinuous_exists_zero_Ioo_of_neg_pos
    (fun x => (hpThetaJensenPolynomial 3 n).eval x) c.x0 c.x1
    c.ordered01 (hpThetaJensenPolynomial 3 n).continuous c.neg0 c.pos1
  obtain ⟨r2, h2, hz2⟩ := hpContinuous_exists_zero_Ioo_of_pos_neg
    (fun x => (hpThetaJensenPolynomial 3 n).eval x) c.x1 c.x2
    c.ordered12 (hpThetaJensenPolynomial 3 n).continuous c.pos1 c.neg2
  obtain ⟨r3, h3, hz3⟩ := hpContinuous_exists_zero_Ioo_of_neg_pos
    (fun x => (hpThetaJensenPolynomial 3 n).eval x) c.x2 c.x3
    c.ordered23 (hpThetaJensenPolynomial 3 n).continuous c.neg2 c.pos3
  exact ⟨r1, r2, r3, h1, h2, h3, lt_trans h1.2 h2.1, lt_trans h2.2 h3.1,
    hpThetaJensenCubic_real_root_neg_allShifts n r3 hz3, hz1, hz2, hz3⟩

private theorem hpCubicCertificate_eval_coefficients (n : ℕ) (x : ℝ) :
    (hpThetaJensenPolynomial 3 n).eval x =
      hpThetaJensenGamma (n + 3) * x ^ 3 + (3 * hpThetaJensenGamma (n + 2)) * x ^ 2 +
      (3 * hpThetaJensenGamma (n + 1)) * x + hpThetaJensenGamma n := by
  rw [hpThetaJensenPolynomial_three_allShifts]
  simp only [Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
  ring

theorem hpThetaJensenCubic_discr_pos_of_signCertificate
    (n : ℕ) (c : hpThetaJensenCubicSignCertificate n) :
    0 < (hpThetaJensenShiftedCubic n).discr := by
  obtain ⟨r1, r2, r3, h1, h2, h3, h12, h23, hneg, hz1, hz2, hz3⟩ :=
    hpThetaJensenCubic_three_distinct_roots_of_signCertificate n c
  rw [hpCubicCertificate_eval_coefficients] at hz1 hz2 hz3
  change 0 < (Cubic.mk (hpThetaJensenGamma (n + 3))
    (3 * hpThetaJensenGamma (n + 2)) (3 * hpThetaJensenGamma (n + 1))
    (hpThetaJensenGamma n)).discr
  exact hpRealCubic_discr_pos_of_three_distinct_roots _ _ _ _ _ _ _
    (ne_of_gt (hpThetaJensenGamma_pos_allShifts (n + 3))) h12 h23 hz1 hz2 hz3

theorem hpThetaJensenHigherTuranGap_pos_of_signCertificate
    (n : ℕ) (c : hpThetaJensenCubicSignCertificate n) :
    0 < hpThetaJensenHigherTuranGap n := by
  have h := hpThetaJensenCubic_discr_pos_of_signCertificate n c
  rw [hpThetaJensenShiftedCubic_discr_eq_higherGap] at h
  nlinarith only [h]

theorem hpThetaDensityWeightedMixedGap_pos_of_signCertificate
    (n : ℕ) (c : hpThetaJensenCubicSignCertificate n) :
    0 < hpThetaDensityWeightedMixedGap (hpThetaDensityJensenExponent n) := by
  exact (hpThetaJensenHigherTuranGap_pos_iff_weightedMixedGap n).mp
    (hpThetaJensenHigherTuranGap_pos_of_signCertificate n c)

theorem hpThetaJensen_sharp_defect_step_of_signCertificate
    (n : ℕ) (c : hpThetaJensenCubicSignCertificate n) :
    |hpThetaJensenReciprocalSqrtDefect n -
      hpThetaJensenReciprocalSqrtDefect (n + 1)| < 1 := by
  exact (hpThetaJensenHigherTuranGap_pos_iff_sharp_defect_step n).mp
    (hpThetaJensenHigherTuranGap_pos_of_signCertificate n c)

theorem hpThetaJensenCubic_realZeros_of_signCertificate
    (n : ℕ) (c : hpThetaJensenCubicSignCertificate n) (z : ℂ)
    (hz : (hpThetaJensenPolynomial 3 n).eval₂ Complex.ofRealHom z = 0) :
    z.im = 0 := by
  exact hpThetaJensenCubic_root_im_zero_of_higherGap n
    (hpThetaJensenHigherTuranGap_pos_of_signCertificate n c) z hz

theorem hpThetaJensenCubic_signCertificate_of_le_two (n : ℕ) (hn : n ≤ 2) :
    Nonempty (hpThetaJensenCubicSignCertificate n) := by
  interval_cases n
  · exact ⟨⟨-90, -55, -42, -15, by norm_num, by norm_num, by norm_num,
      hpThetaJensenCubic_eval_neg90_neg, hpThetaJensenCubic_eval_neg55_pos,
      hpThetaJensenCubic_eval_neg42_neg, hpThetaJensenCubic_eval_neg15_pos⟩⟩
  · exact ⟨⟨-100, -65, -40, -20, by norm_num, by norm_num, by norm_num,
      hpThetaJensenShiftOne_eval_neg100_neg, hpThetaJensenShiftOne_eval_neg65_pos,
      hpThetaJensenShiftOne_eval_neg40_neg, hpThetaJensenShiftOne_eval_neg20_pos⟩⟩
  · exact ⟨⟨-100, -65, -45, -25, by norm_num, by norm_num, by norm_num,
      hpThetaJensenShiftTwo_eval_neg100_neg, hpThetaJensenShiftTwo_eval_neg65_pos,
      hpThetaJensenShiftTwo_eval_neg45_neg, hpThetaJensenShiftTwo_eval_neg25_pos⟩⟩

theorem hpThetaJensenCubic_allShifts_realZeros_of_tail_signCertificates
    (h : ∀ n : ℕ, 3 ≤ n → Nonempty (hpThetaJensenCubicSignCertificate n)) :
    ∀ (n : ℕ) (z : ℂ),
      (hpThetaJensenPolynomial 3 n).eval₂ Complex.ofRealHom z = 0 → z.im = 0 := by
  apply hpThetaJensenCubic_allShifts_realZeros_of_higherGaps
  apply hpThetaJensenHigherTuranGap_all_iff_from_three.mpr
  intro n hn
  obtain ⟨c⟩ := h n hn
  exact hpThetaJensenHigherTuranGap_pos_of_signCertificate n c

#print axioms hpThetaJensenCubic_signs_of_cutoff_margins
#print axioms hpThetaJensenCubic_signCertificate_of_cutoff_margins
#print axioms hpThetaJensenCubic_three_distinct_roots_of_signCertificate
#print axioms hpThetaJensenCubic_discr_pos_of_signCertificate
#print axioms hpThetaJensenHigherTuranGap_pos_of_signCertificate
#print axioms hpThetaDensityWeightedMixedGap_pos_of_signCertificate
#print axioms hpThetaJensen_sharp_defect_step_of_signCertificate
#print axioms hpThetaJensenCubic_realZeros_of_signCertificate
#print axioms hpThetaJensenCubic_signCertificate_of_le_two
#print axioms hpThetaJensenCubic_allShifts_realZeros_of_tail_signCertificates
end HodgeProofHP
