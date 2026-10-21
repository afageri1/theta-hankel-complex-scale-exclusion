/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenDensityScoreMomentComparison

/-!
# Bivariate density kernel and its actual mixed moments

The positive score kernel is symmetric, vanishes on the diagonal, and is
strictly positive off it. Its mixed moments are expressed in real density
moments using the proved score integration-by-parts identities.
The diagonal minor is negative, so pointwise positivity must not be confused
with positivity of all two-by-two kernel minors. No higher-gap sign is assumed.
-/
noncomputable section
open MeasureTheory
namespace HodgeProofHP

def hpThetaDensityBivariateKernel (x y : ℝ) : ℝ :=
  (y - x) * (hpThetaDensityScore y - hpThetaDensityScore x) *
    hpThetaPhiSquareDensity x * hpThetaPhiSquareDensity y

def hpThetaDensityInnerMoment (b x : ℝ) : ℝ :=
  ∫ y in Set.Ioi (0 : ℝ), y ^ b * hpThetaDensityBivariateKernel x y

def hpThetaDensityMixedMoment (a b : ℝ) : ℝ :=
  ∫ x in Set.Ioi (0 : ℝ), x ^ a * hpThetaDensityInnerMoment b x

def hpThetaDensityMomentTuran (p : ℝ) : ℝ :=
  (p + 1) * hpThetaDensityRealMoment p ^ 2 -
    p * hpThetaDensityRealMoment (p - 1) * hpThetaDensityRealMoment (p + 1)

def hpThetaDensityMomentCross (p : ℝ) : ℝ :=
  (p + 2) * hpThetaDensityRealMoment p * hpThetaDensityRealMoment (p + 1) -
    p * hpThetaDensityRealMoment (p - 1) * hpThetaDensityRealMoment (p + 2)

theorem hpThetaDensityBivariateKernel_symm (x y : ℝ) :
    hpThetaDensityBivariateKernel x y = hpThetaDensityBivariateKernel y x := by
  unfold hpThetaDensityBivariateKernel
  ring

theorem hpThetaDensityBivariateKernel_diag (x : ℝ) :
    hpThetaDensityBivariateKernel x x = 0 := by
  simp only [hpThetaDensityBivariateKernel, sub_self, zero_mul]

theorem hpThetaDensityBivariateKernel_pos (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    0 < hpThetaDensityBivariateKernel x y := by
  have hpair : 0 < (y - x) * (hpThetaDensityScore y - hpThetaDensityScore x) := by
    rcases lt_or_gt_of_ne hxy with h | h
    · exact mul_pos (sub_pos.mpr h)
        (sub_pos.mpr (hpThetaDensityScore_strictMonoOn hx hy h))
    · exact mul_pos_of_neg_of_neg (sub_neg.mpr h)
        (sub_neg.mpr (hpThetaDensityScore_strictMonoOn hy hx h))
  exact mul_pos (mul_pos hpair (hpThetaPhiSquareDensity_pos x hx))
    (hpThetaPhiSquareDensity_pos y hy)

theorem hpThetaDensityBivariateKernel_nonneg (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    0 ≤ hpThetaDensityBivariateKernel x y := by
  by_cases hxy : x = y
  · subst y
    rw [hpThetaDensityBivariateKernel_diag]
  · exact (hpThetaDensityBivariateKernel_pos x y hx hy hxy).le

theorem hpThetaDensityBivariateKernel_diagonal_minor_neg (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    hpThetaDensityBivariateKernel x x * hpThetaDensityBivariateKernel y y -
      hpThetaDensityBivariateKernel x y * hpThetaDensityBivariateKernel y x < 0 := by
  rw [hpThetaDensityBivariateKernel_diag, hpThetaDensityBivariateKernel_diag]
  have h := mul_pos (hpThetaDensityBivariateKernel_pos x y hx hy hxy)
    (hpThetaDensityBivariateKernel_pos y x hy hx hxy.symm)
  nlinarith only [h]

private theorem hpDensityMixed_integral_four (f1 f2 f3 f4 : ℝ → ℝ)
    (h1 : IntegrableOn f1 (Set.Ioi 0) volume)
    (h2 : IntegrableOn f2 (Set.Ioi 0) volume)
    (h3 : IntegrableOn f3 (Set.Ioi 0) volume)
    (h4 : IntegrableOn f4 (Set.Ioi 0) volume) :
    (∫ x in Set.Ioi (0 : ℝ), ((f1 - f2 - f3) + f4) x) =
      (∫ x in Set.Ioi (0 : ℝ), f1 x) - (∫ x in Set.Ioi (0 : ℝ), f2 x) -
      (∫ x in Set.Ioi (0 : ℝ), f3 x) + (∫ x in Set.Ioi (0 : ℝ), f4 x) := by
  have h12 := integral_sub h1 h2
  have h123 := integral_sub (h1.sub h2) h3
  have htotal := integral_add ((h1.sub h2).sub h3) h4
  simp only [Pi.sub_apply, Pi.add_apply] at h12 h123 htotal ⊢
  rw [h123, h12] at htotal
  exact htotal

private theorem hpDensityMixed_inner_expand (b x y : ℝ) (hy : 0 < y) :
    y ^ b * hpThetaDensityBivariateKernel x y =
      hpThetaPhiSquareDensity x *
          (hpThetaDensityScore y * (y ^ (b + 1) * hpThetaPhiSquareDensity y)) -
      (hpThetaDensityScore x * hpThetaPhiSquareDensity x) *
          (y ^ (b + 1) * hpThetaPhiSquareDensity y) -
      (x * hpThetaPhiSquareDensity x) *
          (hpThetaDensityScore y * (y ^ b * hpThetaPhiSquareDensity y)) +
      (x * hpThetaDensityScore x * hpThetaPhiSquareDensity x) *
          (y ^ b * hpThetaPhiSquareDensity y) := by
  rw [Real.rpow_add hy, Real.rpow_one]
  unfold hpThetaDensityBivariateKernel
  ring

theorem hpThetaDensityInnerMoment_integrableOn (b x : ℝ) (hb : 0 < b) :
    IntegrableOn (fun y : ℝ => y ^ b * hpThetaDensityBivariateKernel x y)
      (Set.Ioi 0) volume := by
  have h1 := (hpThetaDensityScore_rpowWeight_integrableOn (b + 1) (by linarith)).const_mul
    (hpThetaPhiSquareDensity x)
  have h2 := (hpThetaPhiSquareDensity_rpowMoment_integrableOn (b + 1) (by linarith)).const_mul
    (hpThetaDensityScore x * hpThetaPhiSquareDensity x)
  have h3 := (hpThetaDensityScore_rpowWeight_integrableOn b hb).const_mul
    (x * hpThetaPhiSquareDensity x)
  have h4 := (hpThetaPhiSquareDensity_rpowMoment_integrableOn b (by linarith)).const_mul
    (x * hpThetaDensityScore x * hpThetaPhiSquareDensity x)
  apply Integrable.congr (((h1.sub h2).sub h3).add h4)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact (hpDensityMixed_inner_expand b x y hy).symm

theorem hpThetaDensityInnerMoment_eq (b x : ℝ) (hb : 0 < b) :
    hpThetaDensityInnerMoment b x =
      ((b + 1) * hpThetaDensityRealMoment b) * hpThetaPhiSquareDensity x -
      hpThetaDensityRealMoment (b + 1) *
        (hpThetaDensityScore x * hpThetaPhiSquareDensity x) -
      (b * hpThetaDensityRealMoment (b - 1)) * (x * hpThetaPhiSquareDensity x) +
      hpThetaDensityRealMoment b * (x * hpThetaDensityScore x * hpThetaPhiSquareDensity x) := by
  let f1 : ℝ → ℝ := fun y => hpThetaPhiSquareDensity x *
    (hpThetaDensityScore y * (y ^ (b + 1) * hpThetaPhiSquareDensity y))
  let f2 : ℝ → ℝ := fun y => (hpThetaDensityScore x * hpThetaPhiSquareDensity x) *
    (y ^ (b + 1) * hpThetaPhiSquareDensity y)
  let f3 : ℝ → ℝ := fun y => (x * hpThetaPhiSquareDensity x) *
    (hpThetaDensityScore y * (y ^ b * hpThetaPhiSquareDensity y))
  let f4 : ℝ → ℝ := fun y => (x * hpThetaDensityScore x * hpThetaPhiSquareDensity x) *
    (y ^ b * hpThetaPhiSquareDensity y)
  have h1 : IntegrableOn f1 (Set.Ioi 0) volume :=
    (hpThetaDensityScore_rpowWeight_integrableOn (b + 1) (by linarith)).const_mul _
  have h2 : IntegrableOn f2 (Set.Ioi 0) volume :=
    (hpThetaPhiSquareDensity_rpowMoment_integrableOn (b + 1) (by linarith)).const_mul _
  have h3 : IntegrableOn f3 (Set.Ioi 0) volume :=
    (hpThetaDensityScore_rpowWeight_integrableOn b hb).const_mul _
  have h4 : IntegrableOn f4 (Set.Ioi 0) volume :=
    (hpThetaPhiSquareDensity_rpowMoment_integrableOn b (by linarith)).const_mul _
  have heq : hpThetaDensityInnerMoment b x =
      ∫ y in Set.Ioi (0 : ℝ), ((f1 - f2 - f3) + f4) y := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    exact hpDensityMixed_inner_expand b x y hy
  rw [heq, hpDensityMixed_integral_four f1 f2 f3 f4 h1 h2 h3 h4]
  simp only [f1, f2, f3, f4, integral_const_mul,
    hpThetaDensityScore_rpowWeight_integral b hb,
    hpThetaDensityScore_rpowWeight_integral (b + 1) (by linarith),
    show (b + 1) - 1 = b by ring]
  change hpThetaPhiSquareDensity x * ((b + 1) * hpThetaDensityRealMoment b) -
    (hpThetaDensityScore x * hpThetaPhiSquareDensity x) * hpThetaDensityRealMoment (b + 1) -
    (x * hpThetaPhiSquareDensity x) * (b * hpThetaDensityRealMoment (b - 1)) +
    (x * hpThetaDensityScore x * hpThetaPhiSquareDensity x) * hpThetaDensityRealMoment b = _
  ring

private theorem hpDensityMixed_outer_expand (a b x : ℝ) (ha : 0 < x) (hb : 0 < b) :
    x ^ a * hpThetaDensityInnerMoment b x =
      ((b + 1) * hpThetaDensityRealMoment b) * (x ^ a * hpThetaPhiSquareDensity x) -
      hpThetaDensityRealMoment (b + 1) *
        (hpThetaDensityScore x * (x ^ a * hpThetaPhiSquareDensity x)) -
      (b * hpThetaDensityRealMoment (b - 1)) * (x ^ (a + 1) * hpThetaPhiSquareDensity x) +
      hpThetaDensityRealMoment b *
        (hpThetaDensityScore x * (x ^ (a + 1) * hpThetaPhiSquareDensity x)) := by
  rw [hpThetaDensityInnerMoment_eq b x hb, Real.rpow_add ha, Real.rpow_one]
  ring

theorem hpThetaDensityMixedMoment_integrableOn (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => x ^ a * hpThetaDensityInnerMoment b x)
      (Set.Ioi 0) volume := by
  have h1 := (hpThetaPhiSquareDensity_rpowMoment_integrableOn a (by linarith)).const_mul
    ((b + 1) * hpThetaDensityRealMoment b)
  have h2 := (hpThetaDensityScore_rpowWeight_integrableOn a ha).const_mul
    (hpThetaDensityRealMoment (b + 1))
  have h3 := (hpThetaPhiSquareDensity_rpowMoment_integrableOn (a + 1) (by linarith)).const_mul
    (b * hpThetaDensityRealMoment (b - 1))
  have h4 := (hpThetaDensityScore_rpowWeight_integrableOn (a + 1) (by linarith)).const_mul
    (hpThetaDensityRealMoment b)
  apply Integrable.congr (((h1.sub h2).sub h3).add h4)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (hpDensityMixed_outer_expand a b x hx hb).symm

theorem hpThetaDensityMixedMoment_eq (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    hpThetaDensityMixedMoment a b =
      (a + b + 2) * hpThetaDensityRealMoment a * hpThetaDensityRealMoment b -
      a * hpThetaDensityRealMoment (a - 1) * hpThetaDensityRealMoment (b + 1) -
      b * hpThetaDensityRealMoment (a + 1) * hpThetaDensityRealMoment (b - 1) := by
  let f1 : ℝ → ℝ := fun x => ((b + 1) * hpThetaDensityRealMoment b) *
    (x ^ a * hpThetaPhiSquareDensity x)
  let f2 : ℝ → ℝ := fun x => hpThetaDensityRealMoment (b + 1) *
    (hpThetaDensityScore x * (x ^ a * hpThetaPhiSquareDensity x))
  let f3 : ℝ → ℝ := fun x => (b * hpThetaDensityRealMoment (b - 1)) *
    (x ^ (a + 1) * hpThetaPhiSquareDensity x)
  let f4 : ℝ → ℝ := fun x => hpThetaDensityRealMoment b *
    (hpThetaDensityScore x * (x ^ (a + 1) * hpThetaPhiSquareDensity x))
  have h1 : IntegrableOn f1 (Set.Ioi 0) volume :=
    (hpThetaPhiSquareDensity_rpowMoment_integrableOn a (by linarith)).const_mul _
  have h2 : IntegrableOn f2 (Set.Ioi 0) volume :=
    (hpThetaDensityScore_rpowWeight_integrableOn a ha).const_mul _
  have h3 : IntegrableOn f3 (Set.Ioi 0) volume :=
    (hpThetaPhiSquareDensity_rpowMoment_integrableOn (a + 1) (by linarith)).const_mul _
  have h4 : IntegrableOn f4 (Set.Ioi 0) volume :=
    (hpThetaDensityScore_rpowWeight_integrableOn (a + 1) (by linarith)).const_mul _
  have heq : hpThetaDensityMixedMoment a b =
      ∫ x in Set.Ioi (0 : ℝ), ((f1 - f2 - f3) + f4) x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact hpDensityMixed_outer_expand a b x hx hb
  rw [heq, hpDensityMixed_integral_four f1 f2 f3 f4 h1 h2 h3 h4]
  simp only [f1, f2, f3, f4, integral_const_mul,
    hpThetaDensityScore_rpowWeight_integral a ha,
    hpThetaDensityScore_rpowWeight_integral (a + 1) (by linarith),
    show (a + 1) - 1 = a by ring]
  change ((b + 1) * hpThetaDensityRealMoment b) * hpThetaDensityRealMoment a -
    hpThetaDensityRealMoment (b + 1) * (a * hpThetaDensityRealMoment (a - 1)) -
    (b * hpThetaDensityRealMoment (b - 1)) * hpThetaDensityRealMoment (a + 1) +
    hpThetaDensityRealMoment b * ((a + 1) * hpThetaDensityRealMoment a) = _
  ring

theorem hpThetaDensityMixedMoment_diagonal_eq (p : ℝ) (hp : 0 < p) :
    hpThetaDensityMixedMoment p p = 2 * hpThetaDensityMomentTuran p := by
  rw [hpThetaDensityMixedMoment_eq p p hp hp]
  unfold hpThetaDensityMomentTuran
  ring

theorem hpThetaDensityMixedMoment_adjacent_eq (p : ℝ) (hp : 0 < p) :
    hpThetaDensityMixedMoment (p + 1) p = hpThetaDensityMomentCross p := by
  rw [hpThetaDensityMixedMoment_eq (p + 1) p (by linarith) hp]
  simp only [show (p + 1) - 1 = p by ring, show (p + 1) + 1 = p + 2 by ring]
  unfold hpThetaDensityMomentCross
  ring

theorem hpThetaDensityMixedMoment_symm (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    hpThetaDensityMixedMoment a b = hpThetaDensityMixedMoment b a := by
  rw [hpThetaDensityMixedMoment_eq a b ha hb, hpThetaDensityMixedMoment_eq b a hb ha]
  ring

theorem hpThetaDensityMixedMoment_diagonal_pos (p : ℝ) (hp : 0 < p) :
    0 < hpThetaDensityMixedMoment p p := by
  rw [hpThetaDensityMixedMoment_diagonal_eq p hp]
  exact mul_pos (by norm_num) (sub_pos.mpr (hpThetaDensityRealMoment_strict_inequality p hp))

theorem hpThetaDensityMixedMoment_higher_gap_eq (p : ℝ) (hp : 0 < p) :
    (p + 2) * hpThetaDensityMixedMoment p p *
        hpThetaDensityMixedMoment (p + 1) (p + 1) -
      (p + 1) * hpThetaDensityMixedMoment (p + 1) p ^ 2 =
    4 * (p + 2) * hpThetaDensityMomentTuran p * hpThetaDensityMomentTuran (p + 1) -
      (p + 1) * hpThetaDensityMomentCross p ^ 2 := by
  rw [hpThetaDensityMixedMoment_diagonal_eq p hp,
    hpThetaDensityMixedMoment_diagonal_eq (p + 1) (by linarith),
    hpThetaDensityMixedMoment_adjacent_eq p hp]
  ring

#print axioms hpThetaDensityBivariateKernel_symm
#print axioms hpThetaDensityBivariateKernel_diag
#print axioms hpThetaDensityBivariateKernel_pos
#print axioms hpThetaDensityBivariateKernel_nonneg
#print axioms hpThetaDensityBivariateKernel_diagonal_minor_neg
#print axioms hpThetaDensityInnerMoment_integrableOn
#print axioms hpThetaDensityInnerMoment_eq
#print axioms hpThetaDensityMixedMoment_integrableOn
#print axioms hpThetaDensityMixedMoment_eq
#print axioms hpThetaDensityMixedMoment_diagonal_eq
#print axioms hpThetaDensityMixedMoment_adjacent_eq
#print axioms hpThetaDensityMixedMoment_symm
#print axioms hpThetaDensityMixedMoment_diagonal_pos
#print axioms hpThetaDensityMixedMoment_higher_gap_eq
end HodgeProofHP
