/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCubicIntegral
import HodgeProofHP.Stage7ThetaJensenSixthMomentTailBounds

/-! Absolute tail control for cubic evaluation points with |p| ≤ 90.
The bound reuses the certified sixth moment tail. -/
noncomputable section
open MeasureTheory
namespace HodgeProofHP

theorem hpThetaJensenCubicWeight_abs_le_sixth (p u : ℝ)
    (hp : |p| ≤ 90) (hu : 1 ≤ u) :
    |hpThetaJensenCubicWeight p u| ≤ 10000 * u ^ 6 := by
  have hu0 : 0 ≤ u := by linarith
  have h2 : (1 : ℝ) ≤ u ^ 2 := by nlinarith [sq_nonneg (u - 1)]
  have h4 : u ^ 2 ≤ u ^ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h2) (sq_nonneg u)]
  have h6 : u ^ 4 ≤ u ^ 6 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h2) (pow_nonneg hu0 4)]
  have h16 : (1 : ℝ) ≤ u ^ 6 := le_trans h2 (le_trans h4 h6)
  have hp0 : 0 ≤ |p| := abs_nonneg p
  have hp2 := pow_le_pow_left₀ hp0 hp 2
  have hp3 := pow_le_pow_left₀ hp0 hp 3
  norm_num at hp2 hp3
  have htri : |hpThetaJensenCubicWeight p u| ≤
      1 + (3 * |p| / 2) * u ^ 2 + (|p| ^ 2 / 4) * u ^ 4 +
        (|p| ^ 3 / 120) * u ^ 6 := by
    have h1 := abs_add (1 : ℝ) ((3 * p / 2) * u ^ 2)
    have h2a := abs_add (1 + (3 * p / 2) * u ^ 2) ((p ^ 2 / 4) * u ^ 4)
    have h3a := abs_add (1 + (3 * p / 2) * u ^ 2 + (p ^ 2 / 4) * u ^ 4)
      ((p ^ 3 / 120) * u ^ 6)
    simp only [abs_mul, abs_div, abs_pow, abs_of_nonneg hu0] at h1 h2a h3a
    norm_num at h1 h2a h3a
    unfold hpThetaJensenCubicWeight
    linarith
  have ha : (3 * |p| / 2) * u ^ 2 ≤ 135 * u ^ 6 := by
    have hc : 3 * |p| / 2 ≤ (135 : ℝ) := by linarith
    have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg u)
    nlinarith
  have hb : (|p| ^ 2 / 4) * u ^ 4 ≤ 2025 * u ^ 6 := by
    have hc : |p| ^ 2 / 4 ≤ (2025 : ℝ) := by linarith
    have hm := mul_le_mul_of_nonneg_right hc (pow_nonneg hu0 4)
    nlinarith
  have hc : (|p| ^ 3 / 120) * u ^ 6 ≤ 6075 * u ^ 6 := by
    have hcoef : |p| ^ 3 / 120 ≤ (6075 : ℝ) := by linarith
    exact mul_le_mul_of_nonneg_right hcoef (pow_nonneg hu0 6)
  nlinarith [pow_nonneg hu0 6]

theorem hpThetaJensenCubic_tail_abs_le (p : ℝ) (hp : |p| ≤ 90) :
    |∫ u : ℝ in Set.Ioi 1,
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight p u| ≤
        (1 / 5000 : ℝ) := by
  have hint : IntegrableOn (fun u : ℝ =>
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight p u)
      (Set.Ioi 1) volume := by
    apply (hpThetaJensenCubicWeight_integrableOn p).mono_set
    intro u hu
    exact lt_trans (by norm_num : (0 : ℝ) < 1) hu
  have hmajor : IntegrableOn (fun u : ℝ =>
      10000 * (u ^ 6 * hpRiemannThetaDifferentialKernel u))
      (Set.Ioi 1) volume := by
    apply (hpThetaPhi_sixthMoment_integrableOn.const_mul 10000).mono_set
    intro u hu
    exact lt_trans (by norm_num : (0 : ℝ) < 1) hu
  have hbound : (∫ u : ℝ in Set.Ioi 1,
      |hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight p u|) ≤
      ∫ u : ℝ in Set.Ioi 1,
        10000 * (u ^ 6 * hpRiemannThetaDifferentialKernel u) := by
    have habs : IntegrableOn (fun u : ℝ =>
        |hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight p u|)
        (Set.Ioi 1) volume := by
      simpa only [Real.norm_eq_abs] using hint.norm
    apply integral_mono_ae habs hmajor
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hk := (hpThetaPhi_pos_on_nonnegative u (by linarith [hu])).le
    have hw := hpThetaJensenCubicWeight_abs_le_sixth p u hp (le_of_lt hu)
    rw [abs_mul, abs_of_nonneg hk]
    nlinarith [mul_le_mul_of_nonneg_left hw hk]
  have hn : |∫ u : ℝ in Set.Ioi 1,
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight p u| ≤
      ∫ u : ℝ in Set.Ioi 1,
        |hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight p u| := by
    exact abs_integral_le_integral_abs
  rw [integral_const_mul] at hbound
  have htail := hpThetaJensen_sixthMoment_tail_le_twoEminusEight
  linarith

#print axioms hpThetaJensenCubicWeight_abs_le_sixth
#print axioms hpThetaJensenCubic_tail_abs_le
end HodgeProofHP
