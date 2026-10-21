/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftThreeIntegralPartition
import HodgeProofHP.Stage7ThetaJensenTwelfthMomentTailBounds

/-! Uniform absolute tail bound for shift-three evaluations with |p| at most 100. -/
noncomputable section
open MeasureTheory
namespace HodgeProofHP

theorem hpThetaJensenShiftThreeWeight_abs_le_twelfth (p u : ℝ)
    (hp : |p| ≤ 100) (hu : 1 ≤ u) :
    |hpThetaJensenShiftThreeWeight p u| ≤ 3 * u ^ 12 := by
  have hu0 : 0 ≤ u := by linarith
  have h612 : u ^ 6 ≤ u ^ 12 := pow_le_pow_right₀ hu (by norm_num)
  have h812 : u ^ 8 ≤ u ^ 12 := pow_le_pow_right₀ hu (by norm_num)
  have h1012 : u ^ 10 ≤ u ^ 12 := pow_le_pow_right₀ hu (by norm_num)
  have hc8 : |p / 560| ≤ (1 / 5 : ℝ) := by
    calc
      _ = |p| / 560 := by rw [abs_div]; norm_num
      _ ≤ (100 : ℝ) / 560 := div_le_div_of_nonneg_right hp (by norm_num)
      _ ≤ 1 / 5 := by norm_num
  have hc10 : |p ^ 2 / 10080| ≤ (1 : ℝ) := by
    calc
      _ = |p| ^ 2 / 10080 := by rw [abs_div, abs_pow]; norm_num
      _ ≤ (100 : ℝ) ^ 2 / 10080 :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg p) hp 2) (by norm_num)
      _ ≤ 1 := by norm_num
  have hc12 : |p ^ 3 / 665280| ≤ (8 / 5 : ℝ) := by
    calc
      _ = |p| ^ 3 / 665280 := by rw [abs_div, abs_pow]; norm_num
      _ ≤ (100 : ℝ) ^ 3 / 665280 :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg p) hp 3) (by norm_num)
      _ ≤ 8 / 5 := by norm_num
  have ha : |(1 / 120 : ℝ) * u ^ 6| ≤ (1 / 120 : ℝ) * u ^ 12 := by
    calc
      _ = (1 / 120 : ℝ) * u ^ 6 := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg hu0 6)]
        norm_num
      _ ≤ (1 / 120 : ℝ) * u ^ 12 :=
        mul_le_mul_of_nonneg_left h612 (by norm_num)
  have hb : |(p / 560) * u ^ 8| ≤ (1 / 5 : ℝ) * u ^ 12 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hu0 8)]
    exact mul_le_mul hc8 h812 (pow_nonneg hu0 8) (by norm_num)
  have hc : |(p ^ 2 / 10080) * u ^ 10| ≤ 1 * u ^ 12 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hu0 10)]
    exact mul_le_mul hc10 h1012 (pow_nonneg hu0 10) (by norm_num)
  have hd : |(p ^ 3 / 665280) * u ^ 12| ≤ (8 / 5 : ℝ) * u ^ 12 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hu0 12)]
    exact mul_le_mul_of_nonneg_right hc12 (pow_nonneg hu0 12)
  have h1 := abs_add_le ((1 / 120 : ℝ) * u ^ 6) ((p / 560) * u ^ 8)
  have h2 := abs_add_le ((1 / 120 : ℝ) * u ^ 6 + (p / 560) * u ^ 8)
    ((p ^ 2 / 10080) * u ^ 10)
  have h3 := abs_add_le
    ((1 / 120 : ℝ) * u ^ 6 + (p / 560) * u ^ 8 + (p ^ 2 / 10080) * u ^ 10)
    ((p ^ 3 / 665280) * u ^ 12)
  unfold hpThetaJensenShiftThreeWeight
  nlinarith only [h1, h2, h3, ha, hb, hc, hd, pow_nonneg hu0 12]

theorem hpThetaJensenShiftThree_tail_abs_le (p : ℝ) (hp : |p| ≤ 100) :
    |∫ u : ℝ in Set.Ioi 1,
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight p u| ≤
        (3 / 40000000 : ℝ) := by
  have hint : IntegrableOn (fun u : ℝ =>
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight p u)
      (Set.Ioi 1) volume := by
    apply (hpThetaJensenShiftThreeWeight_integrableOn p).mono_set
    intro u hu
    exact lt_trans (by norm_num : (0 : ℝ) < 1) hu
  have hmajor : IntegrableOn (fun u : ℝ =>
      3 * (u ^ 12 * hpRiemannThetaDifferentialKernel u))
      (Set.Ioi 1) volume := by
    have h6tail : IntegrableOn
        (fun u : ℝ => u ^ 12 * hpRiemannThetaDifferentialKernel u)
        (Set.Ioi 1) volume := by
      apply hpThetaPhi_twelfthMoment_integrableOn.mono_set
      intro u hu
      change 1 < u at hu
      exact lt_trans (by norm_num : (0 : ℝ) < 1) hu
    change Integrable (fun u : ℝ =>
      3 * (u ^ 12 * hpRiemannThetaDifferentialKernel u))
      (volume.restrict (Set.Ioi 1))
    exact h6tail.const_mul 3
  have hbound : (∫ u : ℝ in Set.Ioi 1,
      |hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight p u|) ≤
      ∫ u : ℝ in Set.Ioi 1,
        3 * (u ^ 12 * hpRiemannThetaDifferentialKernel u) := by
    have habs : IntegrableOn (fun u : ℝ =>
        |hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight p u|)
        (Set.Ioi 1) volume := by
      change Integrable (fun u : ℝ =>
        |hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight p u|)
        (volume.restrict (Set.Ioi 1))
      simpa only [Real.norm_eq_abs] using hint.norm
    apply integral_mono_ae habs hmajor
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    change 1 < u at hu
    have hu0 : 0 ≤ u := by linarith
    have hk := (hpThetaPhi_pos_on_nonnegative u hu0).le
    have hw := hpThetaJensenShiftThreeWeight_abs_le_twelfth p u hp (le_of_lt hu)
    rw [abs_mul, abs_of_nonneg hk]
    nlinarith [mul_le_mul_of_nonneg_left hw hk]
  have hn : |∫ u : ℝ in Set.Ioi 1,
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight p u| ≤
      ∫ u : ℝ in Set.Ioi 1,
        |hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftThreeWeight p u| := by
    exact abs_integral_le_integral_abs
  rw [integral_const_mul] at hbound
  have htail := hpThetaJensen_twelfthMoment_tail_le_oneOverFortyMillion
  linarith

#print axioms hpThetaJensenShiftThreeWeight_abs_le_twelfth
#print axioms hpThetaJensenShiftThree_tail_abs_le
end HodgeProofHP
