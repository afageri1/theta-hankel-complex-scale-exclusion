/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage6ThetaPhiAllMomentsIntegrability
import HodgeProofHP.Stage5ThetaJensenTailIntegrals
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Explicit tail bounds for every natural theta moment

The cutoff can grow with the moment order. If R >= m+1 then the existing
kernel exponential rate at R exceeds m. The resulting tail bound is
R^m * A(R) / (k(R)-m), with no finite-moment numerical assumptions.
-/
noncomputable section
open MeasureTheory
namespace HodgeProofHP

theorem hpThetaJensen_natPower_le_shiftedExp_at_cutoff
    (m : ℕ) (R u : ℝ) (hR : 1 ≤ R) (hu : R ≤ u) :
    u ^ m ≤ R ^ m * Real.exp ((m : ℝ) * (u - R)) := by
  have hR0 : 0 ≤ R := by linarith
  have hu0 : 0 ≤ u := le_trans hR0 hu
  have he := Real.add_one_le_exp (u - R)
  have hm := mul_le_mul_of_nonneg_left he hR0
  have hprod := mul_nonneg (sub_nonneg.mpr hR) (sub_nonneg.mpr hu)
  have hue : u ≤ R * Real.exp (u - R) := by nlinarith only [hm, hprod]
  calc
    u ^ m ≤ (R * Real.exp (u - R)) ^ m := pow_le_pow_left₀ hu0 hue m
    _ = R ^ m * Real.exp ((m : ℝ) * (u - R)) := by
      rw [mul_pow, hpThetaKernelUpper_exp_pow, mul_comm (u - R) (m : ℝ)]

theorem hpThetaJensenKernelTailRate_gt_order
    (m : ℕ) (R : ℝ) (hR : (m : ℝ) + 1 ≤ R) :
    (m : ℝ) < hpThetaJensenKernelTailRate R := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hR0 : 0 ≤ R := by linarith
  have he : 1 + 2 * R ≤ Real.exp (2 * R) := by
    linarith only [Real.add_one_le_exp (2 * R)]
  have hmul := mul_le_mul Real.pi_gt_three.le he
    (by linarith : 0 ≤ 1 + 2 * R) Real.pi_pos.le
  unfold hpThetaJensenKernelTailRate
  nlinarith only [hmul, hR, hm0]

def hpThetaJensenNatMomentTailUpper (m : ℕ) (R : ℝ) : ℝ :=
  R ^ m * hpThetaJensenKernelTailAmplitude R / (hpThetaJensenKernelTailRate R - m)

theorem hpThetaJensenNatMomentTailUpper_pos
    (m : ℕ) (R : ℝ) (hR : (m : ℝ) + 1 ≤ R) :
    0 < hpThetaJensenNatMomentTailUpper m R := by
  have hR0 : 0 < R := by
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  unfold hpThetaJensenNatMomentTailUpper
  exact div_pos (mul_pos (pow_pos hR0 m) (hpThetaJensenKernelTailAmplitude_pos R))
    (sub_pos.mpr (hpThetaJensenKernelTailRate_gt_order m R hR))

theorem hpThetaJensen_natMoment_integrand_le_tailEnvelope
    (m : ℕ) (R u : ℝ) (hR : 1 ≤ R) (hu : R ≤ u) :
    u ^ m * hpRiemannThetaDifferentialKernel u ≤
      (R ^ m * hpThetaJensenKernelTailAmplitude R) *
        Real.exp (-(hpThetaJensenKernelTailRate R - m) * (u - R)) := by
  have hR0 : 0 ≤ R := by linarith
  have hu0 : 0 ≤ u := le_trans hR0 hu
  have h := mul_le_mul (hpThetaJensen_natPower_le_shiftedExp_at_cutoff m R u hR hu)
    (hpThetaJensenKernel_le_tailEnvelope R u hR0 hu)
    (hpThetaPhi_pos_on_nonnegative u hu0).le
    (mul_nonneg (pow_nonneg hR0 m) (Real.exp_pos _).le)
  calc
    _ ≤ (R ^ m * Real.exp ((m : ℝ) * (u - R))) *
        (hpThetaJensenKernelTailAmplitude R *
          Real.exp (-hpThetaJensenKernelTailRate R * (u - R))) := h
    _ = (R ^ m * hpThetaJensenKernelTailAmplitude R) *
        (Real.exp ((m : ℝ) * (u - R)) *
          Real.exp (-hpThetaJensenKernelTailRate R * (u - R))) := by ring
    _ = _ := by
      rw [← Real.exp_add,
        show (m : ℝ) * (u - R) + -hpThetaJensenKernelTailRate R * (u - R) =
          -(hpThetaJensenKernelTailRate R - m) * (u - R) by ring]

theorem hpThetaJensen_natMoment_tail_le
    (m : ℕ) (R : ℝ) (hR : (m : ℝ) + 1 ≤ R) :
    (∫ u : ℝ in Set.Ioi R, u ^ m * hpRiemannThetaDifferentialKernel u) ≤
      hpThetaJensenNatMomentTailUpper m R := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hR1 : 1 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  have hint : IntegrableOn (fun u : ℝ => u ^ m * hpRiemannThetaDifferentialKernel u)
      (Set.Ioi R) volume := by
    apply (hpThetaPhi_natMoment_integrableOn m).mono_set
    intro u hu
    exact lt_trans hR0 hu
  have hk := sub_pos.mpr (hpThetaJensenKernelTailRate_gt_order m R hR)
  have hmajor := hpThetaJensen_shiftedExp_integrableOn
    (R ^ m * hpThetaJensenKernelTailAmplitude R) (hpThetaJensenKernelTailRate R - m) R hk
  have hbound : (∫ u : ℝ in Set.Ioi R, u ^ m * hpRiemannThetaDifferentialKernel u) ≤
      ∫ u : ℝ in Set.Ioi R, (R ^ m * hpThetaJensenKernelTailAmplitude R) *
        Real.exp (-(hpThetaJensenKernelTailRate R - m) * (u - R)) := by
    apply integral_mono_ae hint hmajor
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact hpThetaJensen_natMoment_integrand_le_tailEnvelope m R u hR1 hu.le
  rw [hpThetaJensen_shiftedExp_integral _ _ _ hk] at hbound
  exact hbound

theorem hpThetaJensen_abs_coeff_natMoment_tail_le
    (c : ℝ) (m : ℕ) (R : ℝ) (hR : (m : ℝ) + 1 ≤ R) :
    |c * (∫ u : ℝ in Set.Ioi R, u ^ m * hpRiemannThetaDifferentialKernel u)| ≤
      |c| * hpThetaJensenNatMomentTailUpper m R := by
  have hR0 : 0 ≤ R := by
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hn : 0 ≤ ∫ u : ℝ in Set.Ioi R,
      u ^ m * hpRiemannThetaDifferentialKernel u := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := le_trans hR0 hu.le
    exact mul_nonneg (pow_nonneg hu0 m) (hpThetaPhi_pos_on_nonnegative u hu0).le
  rw [abs_mul, abs_of_nonneg hn]
  exact mul_le_mul_of_nonneg_left (hpThetaJensen_natMoment_tail_le m R hR) (abs_nonneg c)

#print axioms hpThetaJensen_natPower_le_shiftedExp_at_cutoff
#print axioms hpThetaJensenKernelTailRate_gt_order
#print axioms hpThetaJensenNatMomentTailUpper_pos
#print axioms hpThetaJensen_natMoment_integrand_le_tailEnvelope
#print axioms hpThetaJensen_natMoment_tail_le
#print axioms hpThetaJensen_abs_coeff_natMoment_tail_le
end HodgeProofHP
