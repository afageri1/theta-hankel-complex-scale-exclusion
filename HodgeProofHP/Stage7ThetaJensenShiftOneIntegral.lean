/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenCubicHigherTuran
import HodgeProofHP.Stage7ThetaJensenCubicSignedCellBounds

/-!
# Direct integration of the shift-one Jensen cubic

Keep the four moments correlated by integrating a single signed weight of
natural degree eight. Pointwise and finite-cell enclosures are proved here;
no numerical evaluation sign or shift-one real-root theorem is asserted.
-/
noncomputable section
open MeasureTheory
namespace HodgeProofHP

def hpThetaJensenShiftOneWeight (p u : ℝ) : ℝ :=
  (1 / 2) * u ^ 2 + (p / 4) * u ^ 4 +
    (p ^ 2 / 40) * u ^ 6 + (p ^ 3 / 1680) * u ^ 8

theorem hpThetaJensenShiftOneWeight_mul_kernel (p u : ℝ) :
    hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight p u =
      (1 / 2) * (u ^ 2 * hpRiemannThetaDifferentialKernel u) +
      (p / 4) * (u ^ 4 * hpRiemannThetaDifferentialKernel u) +
      (p ^ 2 / 40) * (u ^ 6 * hpRiemannThetaDifferentialKernel u) +
      (p ^ 3 / 1680) * (u ^ 8 * hpRiemannThetaDifferentialKernel u) := by
  unfold hpThetaJensenShiftOneWeight
  ring

theorem hpThetaJensenShiftOneWeight_integrableOn (p : ℝ) :
    IntegrableOn (fun u : ℝ =>
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight p u)
      (Set.Ioi 0) volume := by
  have h2 := (hpThetaPhi_natMoment_integrableOn 2).const_mul (1 / 2 : ℝ)
  have h4 := (hpThetaPhi_natMoment_integrableOn 4).const_mul (p / 4)
  have h6 := (hpThetaPhi_natMoment_integrableOn 6).const_mul (p ^ 2 / 40)
  have h8 := (hpThetaPhi_natMoment_integrableOn 8).const_mul (p ^ 3 / 1680)
  simp_rw [hpThetaJensenShiftOneWeight_mul_kernel]
  exact ((h2.add h4).add h6).add h8

theorem hpThetaJensenShiftOne_eval_moments (p : ℝ) :
    (hpThetaJensenPolynomial 3 1).eval p =
      hpThetaPhiEvenMoment 1 / 2 + hpThetaPhiEvenMoment 2 / 4 * p +
      hpThetaPhiEvenMoment 3 / 40 * p ^ 2 +
      hpThetaPhiEvenMoment 4 / 1680 * p ^ 3 := by
  rw [hpThetaJensenPolynomial_three_allShifts]
  simp only [Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
  norm_num [hpThetaJensenGamma]
  <;> ring

theorem hpThetaJensenShiftOne_eval_eq_integral (p : ℝ) :
    (hpThetaJensenPolynomial 3 1).eval p =
      ∫ u : ℝ in Set.Ioi 0,
        hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight p u := by
  have h2 := (hpThetaPhi_natMoment_integrableOn 2).const_mul (1 / 2 : ℝ)
  have h4 := (hpThetaPhi_natMoment_integrableOn 4).const_mul (p / 4)
  have h6 := (hpThetaPhi_natMoment_integrableOn 6).const_mul (p ^ 2 / 40)
  have h8 := (hpThetaPhi_natMoment_integrableOn 8).const_mul (p ^ 3 / 1680)
  simp_rw [hpThetaJensenShiftOneWeight_mul_kernel]
  have hadd4 := integral_add h2 h4
  have hadd6 := integral_add (h2.add h4) h6
  have hadd8 := integral_add ((h2.add h4).add h6) h8
  simp only [Pi.add_apply] at hadd4 hadd6 hadd8
  rw [hadd8, hadd6, hadd4, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, hpThetaJensenShiftOne_eval_moments]
  simp only [hpThetaPhiEvenMoment, Nat.reduceMul]
  ring

theorem hpThetaJensenShiftOne_eval_eq_finite_add_tail (p : ℝ) :
    (hpThetaJensenPolynomial 3 1).eval p =
      (∫ u : ℝ in Set.Ioo 0 1,
        hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight p u) +
      (∫ u : ℝ in Set.Ioi 1,
        hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight p u) := by
  rw [hpThetaJensenShiftOne_eval_eq_integral]
  have h := intervalIntegral.integral_Ioi_sub_Ioi
    (hpThetaJensenShiftOneWeight_integrableOn p) (show (0 : ℝ) ≤ 1 by norm_num)
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_Ioc_eq_integral_Ioo] at h
  linarith

theorem hpThetaJensenShiftOne_signedCellIntegral_bounds
    (p l r KL KU WL WU : ℝ) (hl : 0 ≤ l) (hlr : l ≤ r)
    (hkernel : ∀ u ∈ Set.Icc l r,
      KL ≤ hpRiemannThetaDifferentialKernel u ∧
        hpRiemannThetaDifferentialKernel u ≤ KU)
    (hweight : ∀ u ∈ Set.Icc l r,
      WL ≤ hpThetaJensenShiftOneWeight p u ∧ hpThetaJensenShiftOneWeight p u ≤ WU) :
    min (KL * WL) (KU * WL) * (r - l) ≤
        (∫ u : ℝ in Set.Ioo l r,
          hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight p u) ∧
      (∫ u : ℝ in Set.Ioo l r,
          hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight p u) ≤
        max (KL * WU) (KU * WU) * (r - l) := by
  have hint : IntegrableOn (fun u : ℝ =>
      hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight p u)
      (Set.Ioo l r) volume := by
    apply (hpThetaJensenShiftOneWeight_integrableOn p).mono_set
    intro u hu
    exact lt_of_le_of_lt hl hu.1
  have hfinite : volume (Set.Ioo l r) ≠ ⊤ := by simp
  have hpoint (u : ℝ) (hu : u ∈ Set.Ioo l r) :
      min (KL * WL) (KU * WL) ≤
          hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight p u ∧
        hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight p u ≤
          max (KL * WU) (KU * WU) := by
    have huc : u ∈ Set.Icc l r := ⟨le_of_lt hu.1, le_of_lt hu.2⟩
    have hk := hkernel u huc
    have hw := hweight u huc
    have hu0 : 0 ≤ u := le_trans hl (le_of_lt hu.1)
    exact hpThetaJensen_signedProduct_bounds _ _ KL KU WL WU
      (hpThetaPhi_pos_on_nonnegative u hu0).le hk.1 hk.2 hw.1 hw.2
  constructor
  · have h := setIntegral_ge_of_const_le_real measurableSet_Ioo hfinite
      (fun u hu => (hpoint u hu).1) hint
    rw [Real.volume_real_Ioo_of_le hlr] at h
    exact h
  · have hneg : ∀ u ∈ Set.Ioo l r,
        -(max (KL * WU) (KU * WU)) ≤
          -(hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftOneWeight p u) := by
      intro u hu
      exact neg_le_neg (hpoint u hu).2
    have h := setIntegral_ge_of_const_le_real measurableSet_Ioo hfinite hneg hint.neg
    rw [Real.volume_real_Ioo_of_le hlr, integral_neg] at h
    linarith

#print axioms hpThetaJensenShiftOneWeight_mul_kernel
#print axioms hpThetaJensenShiftOneWeight_integrableOn
#print axioms hpThetaJensenShiftOne_eval_moments
#print axioms hpThetaJensenShiftOne_eval_eq_integral
#print axioms hpThetaJensenShiftOne_eval_eq_finite_add_tail
#print axioms hpThetaJensenShiftOne_signedCellIntegral_bounds
end HodgeProofHP
