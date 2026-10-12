/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCubicIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Signed rectangle integration for the cubic Jensen weight

The theta kernel is nonnegative, while its polynomial weight can have
either sign. Choose the appropriate kernel endpoint using min and max.
This module supplies the integration rule; numerical sums and full
evaluation signs remain separate certificates.
-/
noncomputable section
open MeasureTheory
namespace HodgeProofHP

theorem hpThetaJensen_signedProduct_bounds
    (f w L U A B : ℝ) (hf : 0 ≤ f)
    (hfL : L ≤ f) (hfU : f ≤ U) (hwA : A ≤ w) (hwB : w ≤ B) :
    min (L * A) (U * A) ≤ f * w ∧ f * w ≤ max (L * B) (U * B) := by
  have hlow : min (L * A) (U * A) ≤ f * A := by
    by_cases hA : 0 ≤ A
    · exact le_trans (min_le_left _ _)
        (mul_le_mul_of_nonneg_right hfL hA)
    · exact le_trans (min_le_right _ _)
        (mul_le_mul_of_nonpos_right hfU (le_of_lt (lt_of_not_ge hA)))
  have hupp : f * B ≤ max (L * B) (U * B) := by
    by_cases hB : 0 ≤ B
    · exact le_trans (mul_le_mul_of_nonneg_right hfU hB) (le_max_right _ _)
    · exact le_trans
        (mul_le_mul_of_nonpos_right hfL (le_of_lt (lt_of_not_ge hB)))
        (le_max_left _ _)
  exact ⟨le_trans hlow (mul_le_mul_of_nonneg_left hwA hf),
    le_trans (mul_le_mul_of_nonneg_left hwB hf) hupp⟩

theorem hpThetaJensenCubic_signedCellIntegral_bounds
    (p l r KL KU WL WU : ℝ) (hl : 0 ≤ l) (hlr : l ≤ r)
    (hkernel : ∀ u ∈ Set.Icc l r,
      KL ≤ hpRiemannThetaDifferentialKernel u ∧
        hpRiemannThetaDifferentialKernel u ≤ KU)
    (hweight : ∀ u ∈ Set.Icc l r,
      WL ≤ hpThetaJensenCubicWeight p u ∧ hpThetaJensenCubicWeight p u ≤ WU) :
    min (KL * WL) (KU * WL) * (r - l) ≤
        (∫ u : ℝ in Set.Ioo l r,
          hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight p u) ∧
      (∫ u : ℝ in Set.Ioo l r,
          hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight p u) ≤
        max (KL * WU) (KU * WU) * (r - l) := by
  have hint : IntegrableOn (fun u : ℝ =>
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight p u)
      (Set.Ioo l r) volume := by
    apply (hpThetaJensenCubicWeight_integrableOn p).mono_set
    intro u hu
    exact lt_of_le_of_lt hl hu.1
  have hfinite : volume (Set.Ioo l r) ≠ ⊤ := by simp
  have hpoint (u : ℝ) (hu : u ∈ Set.Ioo l r) :
      min (KL * WL) (KU * WL) ≤
          hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight p u ∧
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight p u ≤
          max (KL * WU) (KU * WU) := by
    have huc : u ∈ Set.Icc l r := ⟨le_of_lt hu.1, le_of_lt hu.2⟩
    have hk := hkernel u huc
    have hw := hweight u huc
    have hu0 : 0 ≤ u := le_trans hl (le_of_lt hu.1)
    exact hpThetaJensen_signedProduct_bounds
      (hpRiemannThetaDifferentialKernel u) (hpThetaJensenCubicWeight p u)
      KL KU WL WU (le_of_lt (hpThetaPhi_pos_on_nonnegative u hu0))
      hk.1 hk.2 hw.1 hw.2
  constructor
  · have h := setIntegral_ge_of_const_le_real measurableSet_Ioo hfinite
      (fun u hu => (hpoint u hu).1) hint
    rw [Real.volume_real_Ioo_of_le hlr] at h
    exact h
  · have hneg : ∀ u ∈ Set.Ioo l r,
        -(max (KL * WU) (KU * WU)) ≤
          -(hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicWeight p u) := by
      intro u hu
      exact neg_le_neg (hpoint u hu).2
    have h := setIntegral_ge_of_const_le_real measurableSet_Ioo hfinite hneg hint.neg
    rw [Real.volume_real_Ioo_of_le hlr, integral_neg] at h
    linarith

#print axioms hpThetaJensen_signedProduct_bounds
#print axioms hpThetaJensenCubic_signedCellIntegral_bounds
end HodgeProofHP
