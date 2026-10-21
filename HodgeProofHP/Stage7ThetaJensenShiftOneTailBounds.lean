/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegral
import HodgeProofHP.Stage7ThetaJensenEighthMomentTailBounds

/-! Uniform absolute tail bound for shift-one evaluations with |p| at most 100. -/
noncomputable section
open MeasureTheory
namespace HodgeProofHP

theorem hpThetaJensenShiftOneWeight_abs_le_eighth (p u : ℝ)
    (hp : |p| ≤ 100) (hu : 1 ≤ u) :
    |hpThetaJensenShiftOneWeight p u| ≤ 1000 * u ^ 8 := by
  have hu0 : 0 ≤ u := by linarith
  have h28 : u ^ 2 ≤ u ^ 8 := pow_le_pow_right₀ hu (by norm_num)
  have h48 : u ^ 4 ≤ u ^ 8 := pow_le_pow_right₀ hu (by norm_num)
  have h68 : u ^ 6 ≤ u ^ 8 := pow_le_pow_right₀ hu (by norm_num)
  have hc4 : |p / 4| ≤ (25 : ℝ) := by
    calc
      _ = |p| / 4 := by rw [abs_div]; norm_num
      _ ≤ (100 : ℝ) / 4 := div_le_div_of_nonneg_right hp (by norm_num)
      _ = 25 := by norm_num
  have hc6 : |p ^ 2 / 40| ≤ (250 : ℝ) := by
    calc
      _ = |p| ^ 2 / 40 := by rw [abs_div, abs_pow]; norm_num
      _ ≤ (100 : ℝ) ^ 2 / 40 :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg p) hp 2) (by norm_num)
      _ = 250 := by norm_num
  have hc8 : |p ^ 3 / 1680| ≤ (600 : ℝ) := by
    calc
      _ = |p| ^ 3 / 1680 := by rw [abs_div, abs_pow]; norm_num
      _ ≤ (100 : ℝ) ^ 3 / 1680 :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg p) hp 3) (by norm_num)
      _ ≤ 600 := by norm_num
  have ha : |(1 / 2 : ℝ) * u ^ 2| ≤ (1 / 2 : ℝ) * u ^ 8 := by
    calc
      _ = (1 / 2 : ℝ) * u ^ 2 := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg hu0 2)]
        norm_num
      _ ≤ (1 / 2 : ℝ) * u ^ 8 := mul_le_mul_of_nonneg_left h28 (by norm_num)
  have hb : |(p / 4) * u ^ 4| ≤ 25 * u ^ 8 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hu0 4)]
    exact mul_le_mul hc4 h48 (pow_nonneg hu0 4) (by norm_num)
  have hc : |(p ^ 2 / 40) * u ^ 6| ≤ 250 * u ^ 8 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hu0 6)]
    exact mul_le_mul hc6 h68 (pow_nonneg hu0 6) (by norm_num)
  have hd : |(p ^ 3 / 1680) * u ^ 8| ≤ 600 * u ^ 8 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hu0 8)]
    exact mul_le_mul_of_nonneg_right hc8 (pow_nonneg hu0 8)
  have h1 := abs_add_le ((1 / 2 : ℝ) * u ^ 2) ((p / 4) * u ^ 4)
  have h2 := abs_add_le ((1 / 2 : ℝ) * u ^ 2 + (p / 4) * u ^ 4)
    ((p ^ 2 / 40) * u ^ 6)
  have h3 := abs_add_le
    ((1 / 2 : ℝ) * u ^ 2 + (p / 4) * u ^ 4 + (p ^ 2 / 40) * u ^ 6)
    ((p ^ 3 / 1680) * u ^ 8)
  unfold hpThetaJensenShiftOneWeight
  nlinarith only [h1, h2, h3, ha, hb, hc, hd, pow_nonneg hu0 8]

theorem hpThetaJensenShiftOne_tail_abs_le (p : ℝ) (hp : |p| ≤ 100) :
    |∫ u : ℝ in Set.Ioi 1,
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight p u| ≤
        (1 / 50000 : ℝ) := by
  have hint : IntegrableOn (fun u : ℝ =>
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight p u)
      (Set.Ioi 1) volume := by
    apply (hpThetaJensenShiftOneWeight_integrableOn p).mono_set
    intro u hu
    exact lt_trans (by norm_num : (0 : ℝ) < 1) hu
  have hmajor : IntegrableOn (fun u : ℝ =>
      1000 * (u ^ 8 * hpRiemannThetaDifferentialKernel u))
      (Set.Ioi 1) volume := by
    have h6tail : IntegrableOn
        (fun u : ℝ => u ^ 8 * hpRiemannThetaDifferentialKernel u)
        (Set.Ioi 1) volume := by
      apply hpThetaPhi_eighthMoment_integrableOn.mono_set
      intro u hu
      change 1 < u at hu
      exact lt_trans (by norm_num : (0 : ℝ) < 1) hu
    change Integrable (fun u : ℝ =>
      1000 * (u ^ 8 * hpRiemannThetaDifferentialKernel u))
      (volume.restrict (Set.Ioi 1))
    exact h6tail.const_mul 1000
  have hbound : (∫ u : ℝ in Set.Ioi 1,
      |hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight p u|) ≤
      ∫ u : ℝ in Set.Ioi 1,
        1000 * (u ^ 8 * hpRiemannThetaDifferentialKernel u) := by
    have habs : IntegrableOn (fun u : ℝ =>
        |hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight p u|)
        (Set.Ioi 1) volume := by
      change Integrable (fun u : ℝ =>
        |hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight p u|)
        (volume.restrict (Set.Ioi 1))
      simpa only [Real.norm_eq_abs] using hint.norm
    apply integral_mono_ae habs hmajor
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    change 1 < u at hu
    have hu0 : 0 ≤ u := by linarith
    have hk := (hpThetaPhi_pos_on_nonnegative u hu0).le
    have hw := hpThetaJensenShiftOneWeight_abs_le_eighth p u hp (le_of_lt hu)
    rw [abs_mul, abs_of_nonneg hk]
    nlinarith [mul_le_mul_of_nonneg_left hw hk]
  have hn : |∫ u : ℝ in Set.Ioi 1,
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight p u| ≤
      ∫ u : ℝ in Set.Ioi 1,
        |hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight p u| := by
    exact abs_integral_le_integral_abs
  rw [integral_const_mul] at hbound
  have htail := hpThetaJensen_eighthMoment_tail_le_twoEminusEight
  linarith

#print axioms hpThetaJensenShiftOneWeight_abs_le_eighth
#print axioms hpThetaJensenShiftOne_tail_abs_le
end HodgeProofHP
