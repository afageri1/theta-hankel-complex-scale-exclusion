/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityBivariateMoments

/-!
# Actual score derivatives and local bivariate differential curvature

The score contrast C(x,y)=(y-x)(q(y)-q(x)) is the actual bivariate
kernel with its two positive density factors removed. Its local mixed
logarithmic curvature is positive away from the diagonal. Nevertheless,
the full kernel has negative diagonal crossing minors, so no global
nonnegative-minor statement follows from the local differential sign.

This distinction matters when analyzing the determinant method of
Dimitrov--Lucas, Proc. AMS 139 (2011), 1013--1022,
DOI 10.1090/S0002-9939-2010-10515-4. No integrated determinant sign
or all-shift cubic conclusion is asserted here.
-/
noncomputable section
namespace HodgeProofHP

def hpThetaDensityScoreDerivative (x : ℝ) : ℝ :=
  hpThetaPhiDensityCurvature (Real.sqrt x) /
    (4 * Real.sqrt x ^ 3 * hpRiemannThetaDifferentialKernel (Real.sqrt x) ^ 2)

theorem hpThetaDensityScore_hasDerivAt (x : ℝ) (hx : 0 < x) :
    HasDerivAt hpThetaDensityScore (hpThetaDensityScoreDerivative x) x := by
  convert (hpThetaPhiSquareDensityLogSlope_hasDerivAt x hx).neg using 1 <;>
    (try funext t) <;>
    simp only [hpThetaDensityScore, hpThetaDensityScoreDerivative,
      Pi.neg_apply, neg_div, neg_neg]

theorem hpThetaDensityScoreDerivative_pos (x : ℝ) (hx : 0 < x) :
    0 < hpThetaDensityScoreDerivative x := by
  unfold hpThetaDensityScoreDerivative
  have hs := Real.sqrt_pos.mpr hx
  have hf := hpThetaPhi_pos_on_nonnegative (Real.sqrt x) hs.le
  exact div_pos (hpThetaPhiDensityCurvature_pos_global (Real.sqrt x) hs)
    (mul_pos (mul_pos (by norm_num) (pow_pos hs 3)) (sq_pos_of_pos hf))

def hpThetaDensityScoreContrast (x y : ℝ) : ℝ :=
  (y - x) * (hpThetaDensityScore y - hpThetaDensityScore x)

def hpThetaDensityScoreContrastFirst (x y : ℝ) : ℝ :=
  -(hpThetaDensityScore y - hpThetaDensityScore x) -
    (y - x) * hpThetaDensityScoreDerivative x

def hpThetaDensityScoreContrastSecond (x y : ℝ) : ℝ :=
  hpThetaDensityScore y - hpThetaDensityScore x +
    (y - x) * hpThetaDensityScoreDerivative y

def hpThetaDensityScoreContrastMixed (x y : ℝ) : ℝ :=
  -hpThetaDensityScoreDerivative x - hpThetaDensityScoreDerivative y

theorem hpThetaDensityBivariateKernel_eq_contrast (x y : ℝ) :
    hpThetaDensityBivariateKernel x y = hpThetaDensityScoreContrast x y *
      hpThetaPhiSquareDensity x * hpThetaPhiSquareDensity y := by
  rfl

theorem hpThetaDensityScoreContrast_pos (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    0 < hpThetaDensityScoreContrast x y := by
  unfold hpThetaDensityScoreContrast
  rcases lt_or_gt_of_ne hxy with h | h
  · exact mul_pos (sub_pos.mpr h)
      (sub_pos.mpr (hpThetaDensityScore_strictMonoOn hx hy h))
  · exact mul_pos_of_neg_of_neg (sub_neg.mpr h)
      (sub_neg.mpr (hpThetaDensityScore_strictMonoOn hy hx h))

theorem hpThetaDensityScoreContrast_first_hasDerivAt (x y : ℝ) (hx : 0 < x) :
    HasDerivAt (fun u => hpThetaDensityScoreContrast u y)
      (hpThetaDensityScoreContrastFirst x y) x := by
  have h := ((hasDerivAt_const x y).sub (hasDerivAt_id x)).mul
    ((hasDerivAt_const x (hpThetaDensityScore y)).sub
      (hpThetaDensityScore_hasDerivAt x hx))
  convert h using 1 <;>
    (try funext u) <;>
    simp only [hpThetaDensityScoreContrast, hpThetaDensityScoreContrastFirst,
      Pi.mul_apply, Pi.sub_apply, Pi.neg_apply, id_eq] <;> ring

theorem hpThetaDensityScoreContrast_second_hasDerivAt (x y : ℝ) (hy : 0 < y) :
    HasDerivAt (hpThetaDensityScoreContrast x)
      (hpThetaDensityScoreContrastSecond x y) y := by
  have h := ((hasDerivAt_id y).sub_const x).mul
    ((hpThetaDensityScore_hasDerivAt y hy).sub_const (hpThetaDensityScore x))
  convert h using 1 <;>
    (try funext u) <;>
    simp only [hpThetaDensityScoreContrast, hpThetaDensityScoreContrastSecond,
      Pi.mul_apply, Pi.sub_apply, Pi.neg_apply, id_eq] <;> ring

theorem hpThetaDensityScoreContrast_mixed_hasDerivAt (x y : ℝ) (hy : 0 < y) :
    HasDerivAt (hpThetaDensityScoreContrastFirst x)
      (hpThetaDensityScoreContrastMixed x y) y := by
  have h := ((hpThetaDensityScore_hasDerivAt y hy).sub_const
    (hpThetaDensityScore x)).neg.sub
      (((hasDerivAt_id y).sub_const x).mul_const (hpThetaDensityScoreDerivative x))
  convert h using 1 <;>
    (try funext u) <;>
    simp only [hpThetaDensityScoreContrastFirst, hpThetaDensityScoreContrastMixed,
      Pi.mul_apply, Pi.sub_apply, Pi.neg_apply, id_eq] <;> ring

theorem hpThetaDensityScoreContrast_mixed_margin_eq (x y : ℝ) :
    hpThetaDensityScoreContrast x y * hpThetaDensityScoreContrastMixed x y -
        hpThetaDensityScoreContrastFirst x y * hpThetaDensityScoreContrastSecond x y =
      (hpThetaDensityScore y - hpThetaDensityScore x) ^ 2 +
        (y - x) ^ 2 * hpThetaDensityScoreDerivative x * hpThetaDensityScoreDerivative y := by
  unfold hpThetaDensityScoreContrast hpThetaDensityScoreContrastFirst
    hpThetaDensityScoreContrastSecond hpThetaDensityScoreContrastMixed
  ring

theorem hpThetaDensityScoreContrast_mixed_margin_pos (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    0 < hpThetaDensityScoreContrast x y * hpThetaDensityScoreContrastMixed x y -
      hpThetaDensityScoreContrastFirst x y * hpThetaDensityScoreContrastSecond x y := by
  rw [hpThetaDensityScoreContrast_mixed_margin_eq]
  have hd : 0 < (y - x) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hxy.symm)
  exact add_pos_of_nonneg_of_pos (sq_nonneg _)
    (mul_pos (mul_pos hd (hpThetaDensityScoreDerivative_pos x hx))
      (hpThetaDensityScoreDerivative_pos y hy))

theorem hpThetaDensityScoreContrast_ratio_hasDerivAt (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    HasDerivAt
      (fun v => hpThetaDensityScoreContrastFirst x v / hpThetaDensityScoreContrast x v)
      ((hpThetaDensityScoreContrast x y * hpThetaDensityScoreContrastMixed x y -
          hpThetaDensityScoreContrastFirst x y * hpThetaDensityScoreContrastSecond x y) /
        hpThetaDensityScoreContrast x y ^ 2) y := by
  have h := (hpThetaDensityScoreContrast_mixed_hasDerivAt x y hy).div
    (hpThetaDensityScoreContrast_second_hasDerivAt x y hy)
    (ne_of_gt (hpThetaDensityScoreContrast_pos x y hx hy hxy))
  convert h using 1 <;> ring

theorem hpThetaDensityScoreContrast_ratio_deriv_pos (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    0 < deriv
      (fun v => hpThetaDensityScoreContrastFirst x v / hpThetaDensityScoreContrast x v)
      y := by
  rw [(hpThetaDensityScoreContrast_ratio_hasDerivAt x y hx hy hxy).deriv]
  exact div_pos (hpThetaDensityScoreContrast_mixed_margin_pos x y hx hy hxy)
    (sq_pos_of_pos (hpThetaDensityScoreContrast_pos x y hx hy hxy))

theorem hpThetaDensityBivariateKernel_not_all_ordered_minors_nonneg :
    ¬ (∀ x1 x2 y1 y2 : ℝ, 0 < x1 → x1 < x2 → 0 < y1 → y1 < y2 →
      0 ≤ hpThetaDensityBivariateKernel x1 y1 * hpThetaDensityBivariateKernel x2 y2 -
        hpThetaDensityBivariateKernel x1 y2 * hpThetaDensityBivariateKernel x2 y1) := by
  intro h
  have hnonneg := h 1 2 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hneg := hpThetaDensityBivariateKernel_diagonal_minor_neg 1 2
    (by norm_num) (by norm_num) (by norm_num)
  linarith only [hnonneg, hneg]

#print axioms hpThetaDensityScore_hasDerivAt
#print axioms hpThetaDensityScoreDerivative_pos
#print axioms hpThetaDensityBivariateKernel_eq_contrast
#print axioms hpThetaDensityScoreContrast_pos
#print axioms hpThetaDensityScoreContrast_first_hasDerivAt
#print axioms hpThetaDensityScoreContrast_second_hasDerivAt
#print axioms hpThetaDensityScoreContrast_mixed_hasDerivAt
#print axioms hpThetaDensityScoreContrast_mixed_margin_eq
#print axioms hpThetaDensityScoreContrast_mixed_margin_pos
#print axioms hpThetaDensityScoreContrast_ratio_hasDerivAt
#print axioms hpThetaDensityScoreContrast_ratio_deriv_pos
#print axioms hpThetaDensityBivariateKernel_not_all_ordered_minors_nonneg
end HodgeProofHP
