/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftTwoIntegralPartition
import HodgeProofHP.Stage7ThetaJensenTenthMomentTailBounds

/-! Uniform absolute tail bound for shift-two evaluations with |p| at most 100. -/
noncomputable section
open MeasureTheory
namespace HodgeProofHP

theorem hpThetaJensenShiftTwoWeight_abs_le_tenth (p u : ℝ)
    (hp : |p| ≤ 100) (hu : 1 ≤ u) :
    |hpThetaJensenShiftTwoWeight p u| ≤ 60 * u ^ 10 := by
  have hu0 : 0 ≤ u := by linarith
  have h410 : u ^ 4 ≤ u ^ 10 := pow_le_pow_right₀ hu (by norm_num)
  have h610 : u ^ 6 ≤ u ^ 10 := pow_le_pow_right₀ hu (by norm_num)
  have h810 : u ^ 8 ≤ u ^ 10 := pow_le_pow_right₀ hu (by norm_num)
  have hc6 : |p / 40| ≤ (5 / 2 : ℝ) := by
    calc
      _ = |p| / 40 := by rw [abs_div]; norm_num
      _ ≤ (100 : ℝ) / 40 := div_le_div_of_nonneg_right hp (by norm_num)
      _ = 5 / 2 := by norm_num
  have hc8 : |p ^ 2 / 560| ≤ (18 : ℝ) := by
    calc
      _ = |p| ^ 2 / 560 := by rw [abs_div, abs_pow]; norm_num
      _ ≤ (100 : ℝ) ^ 2 / 560 :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg p) hp 2) (by norm_num)
      _ ≤ 18 := by norm_num
  have hc10 : |p ^ 3 / 30240| ≤ (34 : ℝ) := by
    calc
      _ = |p| ^ 3 / 30240 := by rw [abs_div, abs_pow]; norm_num
      _ ≤ (100 : ℝ) ^ 3 / 30240 :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg p) hp 3) (by norm_num)
      _ ≤ 34 := by norm_num
  have ha : |(1 / 12 : ℝ) * u ^ 4| ≤ (1 / 12 : ℝ) * u ^ 10 := by
    calc
      _ = (1 / 12 : ℝ) * u ^ 4 := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg hu0 4)]
        norm_num
      _ ≤ (1 / 12 : ℝ) * u ^ 10 :=
        mul_le_mul_of_nonneg_left h410 (by norm_num)
  have hb : |(p / 40) * u ^ 6| ≤ (5 / 2 : ℝ) * u ^ 10 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hu0 6)]
    exact mul_le_mul hc6 h610 (pow_nonneg hu0 6) (by norm_num)
  have hc : |(p ^ 2 / 560) * u ^ 8| ≤ 18 * u ^ 10 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hu0 8)]
    exact mul_le_mul hc8 h810 (pow_nonneg hu0 8) (by norm_num)
  have hd : |(p ^ 3 / 30240) * u ^ 10| ≤ 34 * u ^ 10 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hu0 10)]
    exact mul_le_mul_of_nonneg_right hc10 (pow_nonneg hu0 10)
  have h1 := abs_add_le ((1 / 12 : ℝ) * u ^ 4) ((p / 40) * u ^ 6)
  have h2 := abs_add_le ((1 / 12 : ℝ) * u ^ 4 + (p / 40) * u ^ 6)
    ((p ^ 2 / 560) * u ^ 8)
  have h3 := abs_add_le
    ((1 / 12 : ℝ) * u ^ 4 + (p / 40) * u ^ 6 + (p ^ 2 / 560) * u ^ 8)
    ((p ^ 3 / 30240) * u ^ 10)
  unfold hpThetaJensenShiftTwoWeight
  nlinarith only [h1, h2, h3, ha, hb, hc, hd, pow_nonneg hu0 10]

theorem hpThetaJensenShiftTwo_tail_abs_le (p : ℝ) (hp : |p| ≤ 100) :
    |∫ u : ℝ in Set.Ioi 1,
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight p u| ≤
        (3 / 2000000 : ℝ) := by
  have hint : IntegrableOn (fun u : ℝ =>
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight p u)
      (Set.Ioi 1) volume := by
    apply (hpThetaJensenShiftTwoWeight_integrableOn p).mono_set
    intro u hu
    exact lt_trans (by norm_num : (0 : ℝ) < 1) hu
  have hmajor : IntegrableOn (fun u : ℝ =>
      60 * (u ^ 10 * hpRiemannThetaDifferentialKernel u))
      (Set.Ioi 1) volume := by
    have h6tail : IntegrableOn
        (fun u : ℝ => u ^ 10 * hpRiemannThetaDifferentialKernel u)
        (Set.Ioi 1) volume := by
      apply hpThetaPhi_tenthMoment_integrableOn.mono_set
      intro u hu
      change 1 < u at hu
      exact lt_trans (by norm_num : (0 : ℝ) < 1) hu
    change Integrable (fun u : ℝ =>
      60 * (u ^ 10 * hpRiemannThetaDifferentialKernel u))
      (volume.restrict (Set.Ioi 1))
    exact h6tail.const_mul 60
  have hbound : (∫ u : ℝ in Set.Ioi 1,
      |hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight p u|) ≤
      ∫ u : ℝ in Set.Ioi 1,
        60 * (u ^ 10 * hpRiemannThetaDifferentialKernel u) := by
    have habs : IntegrableOn (fun u : ℝ =>
        |hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight p u|)
        (Set.Ioi 1) volume := by
      change Integrable (fun u : ℝ =>
        |hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight p u|)
        (volume.restrict (Set.Ioi 1))
      simpa only [Real.norm_eq_abs] using hint.norm
    apply integral_mono_ae habs hmajor
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    change 1 < u at hu
    have hu0 : 0 ≤ u := by linarith
    have hk := (hpThetaPhi_pos_on_nonnegative u hu0).le
    have hw := hpThetaJensenShiftTwoWeight_abs_le_tenth p u hp (le_of_lt hu)
    rw [abs_mul, abs_of_nonneg hk]
    nlinarith [mul_le_mul_of_nonneg_left hw hk]
  have hn : |∫ u : ℝ in Set.Ioi 1,
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight p u| ≤
      ∫ u : ℝ in Set.Ioi 1,
        |hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight p u| := by
    exact abs_integral_le_integral_abs
  rw [integral_const_mul] at hbound
  have htail := hpThetaJensen_tenthMoment_tail_le_oneOverFortyMillion
  linarith

#print axioms hpThetaJensenShiftTwoWeight_abs_le_tenth
#print axioms hpThetaJensenShiftTwo_tail_abs_le
end HodgeProofHP
