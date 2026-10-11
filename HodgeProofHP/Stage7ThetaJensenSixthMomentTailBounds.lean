/-
Copyright (c) 2026 Adil Fagiri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adil Fagiri
-/
import HodgeProofHP.Stage6ThetaPhiAllMomentsIntegrability
import HodgeProofHP.Stage5ThetaJensenTailNumericBounds

/-!
# Sixth theta moment: integrability and certified tail

The tail above 1 is bounded by 1/50000000 using the existing kernel
envelope. The finite interval still requires a separate certificate.
No full sixth-moment numerical enclosure or cubic hyperbolicity is assumed.
-/

noncomputable section
open MeasureTheory

namespace HodgeProofHP

theorem hpThetaPhi_sixthMoment_integrableOn :
    IntegrableOn
      (fun u : ℝ => u ^ 6 * hpRiemannThetaDifferentialKernel u)
      (Set.Ioi 0) volume :=
  hpThetaPhi_natMoment_integrableOn 6

theorem hpThetaPhi_sixthMoment_nonneg :
    0 ≤ hpThetaPhiEvenMoment 3 := by
  unfold hpThetaPhiEvenMoment
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact mul_nonneg (pow_nonneg (le_of_lt hu) _)
    (hpThetaPhi_pos_on_nonnegative u (le_of_lt hu)).le

theorem hpThetaJensenKernelTailRate_one_gt_six :
    6 < hpThetaJensenKernelTailRate 1 := by
  linarith [hpThetaJensenKernelTailRate_one_ge_fortyOne]

theorem hpThetaJensen_sixthPower_le_shiftedExp
    (u : ℝ) (hu : 1 ≤ u) :
    u ^ 6 ≤ Real.exp (6 * (u - 1)) := by
  have hu0 : 0 ≤ u := by linarith
  have hue : u ≤ Real.exp (u - 1) := by
    have h := Real.add_one_le_exp (u - 1)
    linarith
  have h := pow_le_pow_left₀ hu0 hue 6
  simpa only [hpThetaKernelUpper_exp_pow, Nat.cast_ofNat, mul_comm] using h

theorem hpThetaJensen_sixthIntegrand_le_tailEnvelope
    (u : ℝ) (hu : 1 ≤ u) :
    u ^ 6 * hpRiemannThetaDifferentialKernel u ≤
      hpThetaJensenKernelTailAmplitude 1 *
        Real.exp (-(hpThetaJensenKernelTailRate 1 - 6) * (u - 1)) := by
  have hu0 : 0 ≤ u := by linarith
  have h := mul_le_mul
    (hpThetaJensen_sixthPower_le_shiftedExp u hu)
    (hpThetaJensenKernel_le_tailEnvelope 1 u (by norm_num) hu)
    (le_of_lt (hpThetaPhi_pos_on_nonnegative u hu0))
    (le_of_lt (Real.exp_pos (6 * (u - 1))))
  calc
    _ ≤ Real.exp (6 * (u - 1)) *
        (hpThetaJensenKernelTailAmplitude 1 *
          Real.exp (-hpThetaJensenKernelTailRate 1 * (u - 1))) := h
    _ = hpThetaJensenKernelTailAmplitude 1 *
        (Real.exp (6 * (u - 1)) *
          Real.exp (-hpThetaJensenKernelTailRate 1 * (u - 1))) := by ring
    _ = _ := by
      rw [← Real.exp_add,
        show 6 * (u - 1) + -hpThetaJensenKernelTailRate 1 * (u - 1) =
          -(hpThetaJensenKernelTailRate 1 - 6) * (u - 1) by ring]

def hpThetaJensenSixthTailUpper : ℝ :=
  hpThetaJensenKernelTailAmplitude 1 / (hpThetaJensenKernelTailRate 1 - 6)

theorem hpThetaJensenSixthTailUpper_pos :
    0 < hpThetaJensenSixthTailUpper := by
  unfold hpThetaJensenSixthTailUpper
  exact div_pos (hpThetaJensenKernelTailAmplitude_pos 1)
    (sub_pos.mpr hpThetaJensenKernelTailRate_one_gt_six)

theorem hpThetaJensen_sixthMoment_tail_le :
    (∫ u : ℝ in Set.Ioi 1, u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
      hpThetaJensenSixthTailUpper := by
  have hint : IntegrableOn
      (fun u : ℝ => u ^ 6 * hpRiemannThetaDifferentialKernel u)
      (Set.Ioi (1 : ℝ)) volume := by
    apply hpThetaPhi_sixthMoment_integrableOn.mono_set
    intro u hu
    change 0 < u
    change 1 < u at hu
    linarith
  have hk : 0 < hpThetaJensenKernelTailRate 1 - 6 :=
    sub_pos.mpr hpThetaJensenKernelTailRate_one_gt_six
  have hmajor := hpThetaJensen_shiftedExp_integrableOn
    (hpThetaJensenKernelTailAmplitude 1) (hpThetaJensenKernelTailRate 1 - 6) 1 hk
  have hbound :
      (∫ u : ℝ in Set.Ioi 1, u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
        ∫ u : ℝ in Set.Ioi 1, hpThetaJensenKernelTailAmplitude 1 *
          Real.exp (-(hpThetaJensenKernelTailRate 1 - 6) * (u - 1)) := by
    apply integral_mono_ae hint hmajor
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact hpThetaJensen_sixthIntegrand_le_tailEnvelope u (le_of_lt hu)
  rw [hpThetaJensen_shiftedExp_integral _ _ _ hk] at hbound
  exact hbound

theorem hpThetaJensenSixthTailUpper_le_twoEminusEight :
    hpThetaJensenSixthTailUpper ≤ (1 / 50000000 : ℝ) := by
  unfold hpThetaJensenSixthTailUpper
  apply (div_le_iff₀ (sub_pos.mpr hpThetaJensenKernelTailRate_one_gt_six)).2
  have hA := hpThetaJensenKernelTailAmplitude_one_le
  have hk := hpThetaJensenKernelTailRate_one_ge_fortyOne
  linarith

theorem hpThetaJensen_sixthMoment_tail_le_twoEminusEight :
    (∫ u : ℝ in Set.Ioi 1, u ^ 6 * hpRiemannThetaDifferentialKernel u) ≤
      (1 / 50000000 : ℝ) :=
  le_trans hpThetaJensen_sixthMoment_tail_le
    hpThetaJensenSixthTailUpper_le_twoEminusEight

#print axioms hpThetaPhi_sixthMoment_integrableOn
#print axioms hpThetaPhi_sixthMoment_nonneg
#print axioms hpThetaJensenKernelTailRate_one_gt_six
#print axioms hpThetaJensen_sixthPower_le_shiftedExp
#print axioms hpThetaJensen_sixthIntegrand_le_tailEnvelope
#print axioms hpThetaJensenSixthTailUpper_pos
#print axioms hpThetaJensen_sixthMoment_tail_le
#print axioms hpThetaJensenSixthTailUpper_le_twoEminusEight
#print axioms hpThetaJensen_sixthMoment_tail_le_twoEminusEight

end HodgeProofHP
