/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage6ThetaPhiAllMomentsIntegrability
import HodgeProofHP.Stage5ThetaJensenTailNumericBounds

/-!
# Tenth theta moment: integrability and certified tail

The tail above 1 is bounded by 1/40000000 using the existing kernel
envelope. The finite interval still requires a separate certificate.
No full tenth-moment numerical enclosure is asserted.
-/

noncomputable section
open MeasureTheory

namespace HodgeProofHP

theorem hpThetaPhi_tenthMoment_integrableOn :
    IntegrableOn
      (fun u : ℝ => u ^ 10 * hpRiemannThetaDifferentialKernel u)
      (Set.Ioi 0) volume :=
  hpThetaPhi_natMoment_integrableOn 10

theorem hpThetaPhi_tenthMoment_nonneg :
    0 ≤ hpThetaPhiEvenMoment 5 := by
  unfold hpThetaPhiEvenMoment
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact mul_nonneg (pow_nonneg (le_of_lt hu) _)
    (hpThetaPhi_pos_on_nonnegative u (le_of_lt hu)).le

theorem hpThetaJensenKernelTailRate_one_gt_ten :
    10 < hpThetaJensenKernelTailRate 1 := by
  linarith [hpThetaJensenKernelTailRate_one_ge_fortyOne]

theorem hpThetaJensen_tenthPower_le_shiftedExp
    (u : ℝ) (hu : 1 ≤ u) :
    u ^ 10 ≤ Real.exp (10 * (u - 1)) := by
  have hu0 : 0 ≤ u := by linarith
  have hue : u ≤ Real.exp (u - 1) := by
    have h := Real.add_one_le_exp (u - 1)
    linarith
  have h := pow_le_pow_left₀ hu0 hue 10
  simpa only [hpThetaKernelUpper_exp_pow, Nat.cast_ofNat, mul_comm] using h

theorem hpThetaJensen_tenthIntegrand_le_tailEnvelope
    (u : ℝ) (hu : 1 ≤ u) :
    u ^ 10 * hpRiemannThetaDifferentialKernel u ≤
      hpThetaJensenKernelTailAmplitude 1 *
        Real.exp (-(hpThetaJensenKernelTailRate 1 - 10) * (u - 1)) := by
  have hu0 : 0 ≤ u := by linarith
  have h := mul_le_mul
    (hpThetaJensen_tenthPower_le_shiftedExp u hu)
    (hpThetaJensenKernel_le_tailEnvelope 1 u (by norm_num) hu)
    (le_of_lt (hpThetaPhi_pos_on_nonnegative u hu0))
    (le_of_lt (Real.exp_pos (10 * (u - 1))))
  calc
    _ ≤ Real.exp (10 * (u - 1)) *
        (hpThetaJensenKernelTailAmplitude 1 *
          Real.exp (-hpThetaJensenKernelTailRate 1 * (u - 1))) := h
    _ = hpThetaJensenKernelTailAmplitude 1 *
        (Real.exp (10 * (u - 1)) *
          Real.exp (-hpThetaJensenKernelTailRate 1 * (u - 1))) := by ring
    _ = _ := by
      rw [← Real.exp_add,
        show 10 * (u - 1) + -hpThetaJensenKernelTailRate 1 * (u - 1) =
          -(hpThetaJensenKernelTailRate 1 - 10) * (u - 1) by ring]

def hpThetaJensenTenthTailUpper : ℝ :=
  hpThetaJensenKernelTailAmplitude 1 / (hpThetaJensenKernelTailRate 1 - 10)

theorem hpThetaJensenTenthTailUpper_pos :
    0 < hpThetaJensenTenthTailUpper := by
  unfold hpThetaJensenTenthTailUpper
  exact div_pos (hpThetaJensenKernelTailAmplitude_pos 1)
    (sub_pos.mpr hpThetaJensenKernelTailRate_one_gt_ten)

theorem hpThetaJensen_tenthMoment_tail_le :
    (∫ u : ℝ in Set.Ioi 1, u ^ 10 * hpRiemannThetaDifferentialKernel u) ≤
      hpThetaJensenTenthTailUpper := by
  have hint : IntegrableOn
      (fun u : ℝ => u ^ 10 * hpRiemannThetaDifferentialKernel u)
      (Set.Ioi (1 : ℝ)) volume := by
    apply hpThetaPhi_tenthMoment_integrableOn.mono_set
    intro u hu
    change 0 < u
    change 1 < u at hu
    linarith
  have hk : 0 < hpThetaJensenKernelTailRate 1 - 10 :=
    sub_pos.mpr hpThetaJensenKernelTailRate_one_gt_ten
  have hmajor := hpThetaJensen_shiftedExp_integrableOn
    (hpThetaJensenKernelTailAmplitude 1) (hpThetaJensenKernelTailRate 1 - 10) 1 hk
  have hbound :
      (∫ u : ℝ in Set.Ioi 1, u ^ 10 * hpRiemannThetaDifferentialKernel u) ≤
        ∫ u : ℝ in Set.Ioi 1, hpThetaJensenKernelTailAmplitude 1 *
          Real.exp (-(hpThetaJensenKernelTailRate 1 - 10) * (u - 1)) := by
    apply integral_mono_ae hint hmajor
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact hpThetaJensen_tenthIntegrand_le_tailEnvelope u (le_of_lt hu)
  rw [hpThetaJensen_shiftedExp_integral _ _ _ hk] at hbound
  exact hbound

theorem hpThetaJensenTenthTailUpper_le_oneOverFortyMillion :
    hpThetaJensenTenthTailUpper ≤ (1 / 40000000 : ℝ) := by
  unfold hpThetaJensenTenthTailUpper
  apply (div_le_iff₀ (sub_pos.mpr hpThetaJensenKernelTailRate_one_gt_ten)).2
  have hA := hpThetaJensenKernelTailAmplitude_one_le
  have hk := hpThetaJensenKernelTailRate_one_ge_fortyOne
  linarith

theorem hpThetaJensen_tenthMoment_tail_le_oneOverFortyMillion :
    (∫ u : ℝ in Set.Ioi 1, u ^ 10 * hpRiemannThetaDifferentialKernel u) ≤
      (1 / 40000000 : ℝ) :=
  le_trans hpThetaJensen_tenthMoment_tail_le
    hpThetaJensenTenthTailUpper_le_oneOverFortyMillion

#print axioms hpThetaPhi_tenthMoment_integrableOn
#print axioms hpThetaPhi_tenthMoment_nonneg
#print axioms hpThetaJensenKernelTailRate_one_gt_ten
#print axioms hpThetaJensen_tenthPower_le_shiftedExp
#print axioms hpThetaJensen_tenthIntegrand_le_tailEnvelope
#print axioms hpThetaJensenTenthTailUpper_pos
#print axioms hpThetaJensen_tenthMoment_tail_le
#print axioms hpThetaJensenTenthTailUpper_le_oneOverFortyMillion
#print axioms hpThetaJensen_tenthMoment_tail_le_oneOverFortyMillion

end HodgeProofHP
