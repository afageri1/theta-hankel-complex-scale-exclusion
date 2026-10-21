/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage7ThetaJensenShiftOneIntegral
import HodgeProofHP.Stage7ThetaJensenTuranMomentEquivalence

/-!
# A single signed integral formula for every natural cubic Jensen shift

The weight has degree at most 2*n+6. All moments are integrable, and every
shift admits finite-and-tail decomposition and signed cell estimates.
The weights at shifts zero and one agree with the previously used definitions.
An explicit shift-two weight is supplied for subsequent numerical certificates.
No new shift-two or all-shift hyperbolicity conclusion is asserted.
-/
noncomputable section
open MeasureTheory
namespace HodgeProofHP

def hpThetaJensenCubicShiftWeight (n : ℕ) (p u : ℝ) : ℝ :=
  hpThetaJensenMomentScale n * u ^ (2 * n) +
    (3 * p * hpThetaJensenMomentScale (n + 1)) * u ^ (2 * (n + 1)) +
    (3 * p ^ 2 * hpThetaJensenMomentScale (n + 2)) * u ^ (2 * (n + 2)) +
    (p ^ 3 * hpThetaJensenMomentScale (n + 3)) * u ^ (2 * (n + 3))

def hpThetaJensenShiftTwoWeight (p u : ℝ) : ℝ :=
  (1 / 12) * u ^ 4 + (p / 40) * u ^ 6 +
    (p ^ 2 / 560) * u ^ 8 + (p ^ 3 / 30240) * u ^ 10

theorem hpThetaJensenCubicShiftWeight_mul_kernel (n : ℕ) (p u : ℝ) :
    hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicShiftWeight n p u =
      hpThetaJensenMomentScale n *
        (u ^ (2 * n) * hpRiemannThetaDifferentialKernel u) +
      (3 * p * hpThetaJensenMomentScale (n + 1)) *
        (u ^ (2 * (n + 1)) * hpRiemannThetaDifferentialKernel u) +
      (3 * p ^ 2 * hpThetaJensenMomentScale (n + 2)) *
        (u ^ (2 * (n + 2)) * hpRiemannThetaDifferentialKernel u) +
      (p ^ 3 * hpThetaJensenMomentScale (n + 3)) *
        (u ^ (2 * (n + 3)) * hpRiemannThetaDifferentialKernel u) := by
  unfold hpThetaJensenCubicShiftWeight
  ring

theorem hpThetaJensenCubicShiftWeight_integrableOn (n : ℕ) (p : ℝ) :
    IntegrableOn (fun u : ℝ =>
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicShiftWeight n p u)
      (Set.Ioi 0) volume := by
  have h0 := (hpThetaPhi_evenMoment_integrableOn n).const_mul
    (hpThetaJensenMomentScale n)
  have h1 := (hpThetaPhi_evenMoment_integrableOn (n + 1)).const_mul
    (3 * p * hpThetaJensenMomentScale (n + 1))
  have h2 := (hpThetaPhi_evenMoment_integrableOn (n + 2)).const_mul
    (3 * p ^ 2 * hpThetaJensenMomentScale (n + 2))
  have h3 := (hpThetaPhi_evenMoment_integrableOn (n + 3)).const_mul
    (p ^ 3 * hpThetaJensenMomentScale (n + 3))
  simp_rw [hpThetaJensenCubicShiftWeight_mul_kernel]
  exact ((h0.add h1).add h2).add h3

theorem hpThetaJensenCubicShift_eval_scaled_moments (n : ℕ) (p : ℝ) :
    (hpThetaJensenPolynomial 3 n).eval p =
      hpThetaJensenMomentScale n * hpThetaPhiEvenMoment n +
      (3 * p * hpThetaJensenMomentScale (n + 1)) * hpThetaPhiEvenMoment (n + 1) +
      (3 * p ^ 2 * hpThetaJensenMomentScale (n + 2)) * hpThetaPhiEvenMoment (n + 2) +
      (p ^ 3 * hpThetaJensenMomentScale (n + 3)) * hpThetaPhiEvenMoment (n + 3) := by
  rw [hpThetaJensenPolynomial_three_allShifts]
  simp only [Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
  unfold hpThetaJensenGamma hpThetaJensenMomentScale
  ring

theorem hpThetaJensenCubicShift_eval_eq_integral (n : ℕ) (p : ℝ) :
    (hpThetaJensenPolynomial 3 n).eval p =
      ∫ u : ℝ in Set.Ioi 0,
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicShiftWeight n p u := by
  have h0 := (hpThetaPhi_evenMoment_integrableOn n).const_mul
    (hpThetaJensenMomentScale n)
  have h1 := (hpThetaPhi_evenMoment_integrableOn (n + 1)).const_mul
    (3 * p * hpThetaJensenMomentScale (n + 1))
  have h2 := (hpThetaPhi_evenMoment_integrableOn (n + 2)).const_mul
    (3 * p ^ 2 * hpThetaJensenMomentScale (n + 2))
  have h3 := (hpThetaPhi_evenMoment_integrableOn (n + 3)).const_mul
    (p ^ 3 * hpThetaJensenMomentScale (n + 3))
  simp_rw [hpThetaJensenCubicShiftWeight_mul_kernel]
  have hadd1 := integral_add h0 h1
  have hadd2 := integral_add (h0.add h1) h2
  have hadd3 := integral_add ((h0.add h1).add h2) h3
  simp only [Pi.add_apply] at hadd1 hadd2 hadd3
  rw [hadd3, hadd2, hadd1, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, hpThetaJensenCubicShift_eval_scaled_moments]
  rfl

theorem hpThetaJensenCubicShift_eval_eq_finite_add_tail (n : ℕ) (p : ℝ) :
    (hpThetaJensenPolynomial 3 n).eval p =
      (∫ u : ℝ in Set.Ioo 0 1,
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicShiftWeight n p u) +
      (∫ u : ℝ in Set.Ioi 1,
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicShiftWeight n p u) := by
  rw [hpThetaJensenCubicShift_eval_eq_integral]
  have h := intervalIntegral.integral_Ioi_sub_Ioi
    (hpThetaJensenCubicShiftWeight_integrableOn n p) (show (0 : ℝ) ≤ 1 by norm_num)
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_Ioc_eq_integral_Ioo] at h
  linarith

theorem hpThetaJensenCubicShift_signedCellIntegral_bounds
    (n : ℕ) (p l r KL KU WL WU : ℝ) (hl : 0 ≤ l) (hlr : l ≤ r)
    (hkernel : ∀ u ∈ Set.Icc l r,
      KL ≤ hpRiemannThetaDifferentialKernel u ∧
        hpRiemannThetaDifferentialKernel u ≤ KU)
    (hweight : ∀ u ∈ Set.Icc l r,
      WL ≤ hpThetaJensenCubicShiftWeight n p u ∧ hpThetaJensenCubicShiftWeight n p u ≤ WU) :
    min (KL * WL) (KU * WL) * (r - l) ≤
        (∫ u : ℝ in Set.Ioo l r,
          hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicShiftWeight n p u) ∧
      (∫ u : ℝ in Set.Ioo l r,
          hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicShiftWeight n p u) ≤
        max (KL * WU) (KU * WU) * (r - l) := by
  have hint : IntegrableOn (fun u : ℝ =>
      hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicShiftWeight n p u)
      (Set.Ioo l r) volume := by
    apply (hpThetaJensenCubicShiftWeight_integrableOn n p).mono_set
    intro u hu
    exact lt_of_le_of_lt hl hu.1
  have hfinite : volume (Set.Ioo l r) ≠ ⊤ := by simp
  have hpoint (u : ℝ) (hu : u ∈ Set.Ioo l r) :
      min (KL * WL) (KU * WL) ≤
          hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicShiftWeight n p u ∧
        hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicShiftWeight n p u ≤
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
          -(hpRiemannThetaDifferentialKernel u * hpThetaJensenCubicShiftWeight n p u) := by
      intro u hu
      exact neg_le_neg (hpoint u hu).2
    have h := setIntegral_ge_of_const_le_real measurableSet_Ioo hfinite hneg hint.neg
    rw [Real.volume_real_Ioo_of_le hlr, integral_neg] at h
    linarith

theorem hpThetaJensenCubicShiftWeight_zero (p u : ℝ) :
    hpThetaJensenCubicShiftWeight 0 p u = hpThetaJensenCubicWeight p u := by
  norm_num [hpThetaJensenCubicShiftWeight, hpThetaJensenMomentScale,
    hpThetaJensenCubicWeight]
  <;> ring

theorem hpThetaJensenCubicShiftWeight_one (p u : ℝ) :
    hpThetaJensenCubicShiftWeight 1 p u = hpThetaJensenShiftOneWeight p u := by
  norm_num [hpThetaJensenCubicShiftWeight, hpThetaJensenMomentScale,
    hpThetaJensenShiftOneWeight]
  <;> ring

theorem hpThetaJensenCubicShiftWeight_two (p u : ℝ) :
    hpThetaJensenCubicShiftWeight 2 p u = hpThetaJensenShiftTwoWeight p u := by
  norm_num [hpThetaJensenCubicShiftWeight, hpThetaJensenMomentScale,
    hpThetaJensenShiftTwoWeight]
  <;> ring

theorem hpThetaJensenShiftTwo_eval_eq_integral (p : ℝ) :
    (hpThetaJensenPolynomial 3 2).eval p =
      ∫ u : ℝ in Set.Ioi 0,
        hpRiemannThetaDifferentialKernel u * hpThetaJensenShiftTwoWeight p u := by
  rw [hpThetaJensenCubicShift_eval_eq_integral]
  simp_rw [hpThetaJensenCubicShiftWeight_two]

#print axioms hpThetaJensenCubicShiftWeight_mul_kernel
#print axioms hpThetaJensenCubicShiftWeight_integrableOn
#print axioms hpThetaJensenCubicShift_eval_scaled_moments
#print axioms hpThetaJensenCubicShift_eval_eq_integral
#print axioms hpThetaJensenCubicShift_eval_eq_finite_add_tail
#print axioms hpThetaJensenCubicShift_signedCellIntegral_bounds
#print axioms hpThetaJensenCubicShiftWeight_zero
#print axioms hpThetaJensenCubicShiftWeight_one
#print axioms hpThetaJensenCubicShiftWeight_two
#print axioms hpThetaJensenShiftTwo_eval_eq_integral
end HodgeProofHP
