import HodgeProofHP.Stage5ThetaJensenKernelBounds
import HodgeProofHP.Stage4ThetaPhiFourthMomentIntegrability
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
# Integrated theta-kernel tail bounds

For u >= 1, u^4 <= exp(4*(u-1)). Thus the previously proved
kernel envelope integrates to A/k for the zero moment and A/(k-4)
for the fourth moment. This latter bound is slightly looser than the
polynomial integral used in the initial Python audit, but still fits
its target M4 <= 3/1000. No numerical data are imported here.
-/

noncomputable section

open MeasureTheory

namespace HodgeProofHP

theorem hpThetaJensen_shiftedExp_integrableOn
    (A k p : ℝ) (hk : 0 < k) :
    IntegrableOn (fun u : ℝ => A * Real.exp (-k * (u - p)))
      (Set.Ioi p) volume := by
  have hfun : (fun u : ℝ => A * Real.exp (-k * (u - p))) =
      (fun u : ℝ => (A * Real.exp (k * p)) * Real.exp ((-k) * u)) := by
    funext u
    rw [show -k * (u - p) = k * p + (-k) * u by ring, Real.exp_add]
    ring
  rw [hfun]
  exact (integrableOn_exp_mul_Ioi (by linarith : -k < 0) p).const_mul _

theorem hpThetaJensen_shiftedExp_integral
    (A k p : ℝ) (hk : 0 < k) :
    (∫ u : ℝ in Set.Ioi p, A * Real.exp (-k * (u - p))) = A / k := by
  have hfun : (fun u : ℝ => A * Real.exp (-k * (u - p))) =
      (fun u : ℝ => (A * Real.exp (k * p)) * Real.exp ((-k) * u)) := by
    funext u
    rw [show -k * (u - p) = k * p + (-k) * u by ring, Real.exp_add]
    ring
  rw [hfun, integral_const_mul, integral_exp_mul_Ioi (by linarith : -k < 0) p]
  calc
    (A * Real.exp (k * p)) * (-Real.exp ((-k) * p) / (-k)) =
        A * (Real.exp (k * p) * Real.exp ((-k) * p)) / k := by ring
    _ = A / k := by
      rw [← Real.exp_add, show k * p + (-k) * p = 0 by ring, Real.exp_zero]
      ring

theorem hpThetaJensenKernelTailRate_one_gt_four :
    4 < hpThetaJensenKernelTailRate 1 := by
  have he : (3 : ℝ) ≤ Real.exp 2 := by
    have h := Real.add_one_le_exp (2 : ℝ)
    linarith
  have hmul := mul_le_mul_of_nonneg_left he (le_of_lt Real.pi_pos)
  have hpi := Real.pi_gt_three
  unfold hpThetaJensenKernelTailRate
  norm_num at hmul ⊢
  nlinarith

theorem hpThetaJensen_fourthPower_le_shiftedExp
    (u : ℝ) (hu : 1 ≤ u) :
    u ^ 4 ≤ Real.exp (4 * (u - 1)) := by
  have hu0 : 0 ≤ u := by linarith
  have hue : u ≤ Real.exp (u - 1) := by
    have h := Real.add_one_le_exp (u - 1)
    linarith
  have h := pow_le_pow_left₀ hu0 hue 4
  simpa only [hpThetaKernelUpper_exp_pow, Nat.cast_ofNat, mul_comm] using h

theorem hpThetaJensen_fourthIntegrand_le_tailEnvelope
    (u : ℝ) (hu : 1 ≤ u) :
    u ^ 4 * hpRiemannThetaDifferentialKernel u ≤
      hpThetaJensenKernelTailAmplitude 1 *
        Real.exp (-(hpThetaJensenKernelTailRate 1 - 4) * (u - 1)) := by
  have hu0 : 0 ≤ u := by linarith
  have h := mul_le_mul
    (hpThetaJensen_fourthPower_le_shiftedExp u hu)
    (hpThetaJensenKernel_le_tailEnvelope 1 u (by norm_num) hu)
    (le_of_lt (hpThetaPhi_pos_on_nonnegative u hu0))
    (le_of_lt (Real.exp_pos (4 * (u - 1))))
  calc
    _ ≤ Real.exp (4 * (u - 1)) *
        (hpThetaJensenKernelTailAmplitude 1 *
          Real.exp (-hpThetaJensenKernelTailRate 1 * (u - 1))) := h
    _ = hpThetaJensenKernelTailAmplitude 1 *
        (Real.exp (4 * (u - 1)) *
          Real.exp (-hpThetaJensenKernelTailRate 1 * (u - 1))) := by ring
    _ = _ := by
      rw [← Real.exp_add,
        show 4 * (u - 1) + -hpThetaJensenKernelTailRate 1 * (u - 1) =
          -(hpThetaJensenKernelTailRate 1 - 4) * (u - 1) by ring]

def hpThetaJensenZeroTailUpper : ℝ :=
  hpThetaJensenKernelTailAmplitude 1 / hpThetaJensenKernelTailRate 1

def hpThetaJensenFourthTailUpper : ℝ :=
  hpThetaJensenKernelTailAmplitude 1 / (hpThetaJensenKernelTailRate 1 - 4)

theorem hpThetaJensenZeroTailUpper_pos : 0 < hpThetaJensenZeroTailUpper := by
  unfold hpThetaJensenZeroTailUpper
  exact div_pos (hpThetaJensenKernelTailAmplitude_pos 1)
    (hpThetaJensenKernelTailRate_pos 1 (by norm_num))

theorem hpThetaJensenFourthTailUpper_pos : 0 < hpThetaJensenFourthTailUpper := by
  unfold hpThetaJensenFourthTailUpper
  exact div_pos (hpThetaJensenKernelTailAmplitude_pos 1)
    (sub_pos.mpr hpThetaJensenKernelTailRate_one_gt_four)

theorem hpThetaJensen_zeroMoment_tail_le :
    (∫ u : ℝ in Set.Ioi 1, hpRiemannThetaDifferentialKernel u) ≤
      hpThetaJensenZeroTailUpper := by
  have hint : IntegrableOn hpRiemannThetaDifferentialKernel
      (Set.Ioi (1 : ℝ)) volume := by
    apply hpThetaPhi_integrableOn.mono_set
    intro u hu
    change 0 < u
    change 1 < u at hu
    linarith
  have hk := hpThetaJensenKernelTailRate_pos 1 (by norm_num)
  have hmajor := hpThetaJensen_shiftedExp_integrableOn
    (hpThetaJensenKernelTailAmplitude 1) (hpThetaJensenKernelTailRate 1) 1 hk
  have hbound :
      (∫ u : ℝ in Set.Ioi 1, hpRiemannThetaDifferentialKernel u) ≤
        ∫ u : ℝ in Set.Ioi 1, hpThetaJensenKernelTailAmplitude 1 *
          Real.exp (-hpThetaJensenKernelTailRate 1 * (u - 1)) := by
    apply integral_mono_ae hint hmajor
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact hpThetaJensenKernel_le_tailEnvelope 1 u (by norm_num) (le_of_lt hu)
  rw [hpThetaJensen_shiftedExp_integral _ _ _ hk] at hbound
  exact hbound

theorem hpThetaJensen_fourthMoment_tail_le :
    (∫ u : ℝ in Set.Ioi 1, u ^ 4 * hpRiemannThetaDifferentialKernel u) ≤
      hpThetaJensenFourthTailUpper := by
  have hint : IntegrableOn
      (fun u : ℝ => u ^ 4 * hpRiemannThetaDifferentialKernel u)
      (Set.Ioi (1 : ℝ)) volume := by
    apply hpThetaPhi_fourthMoment_integrableOn.mono_set
    intro u hu
    change 0 < u
    change 1 < u at hu
    linarith
  have hk : 0 < hpThetaJensenKernelTailRate 1 - 4 :=
    sub_pos.mpr hpThetaJensenKernelTailRate_one_gt_four
  have hmajor := hpThetaJensen_shiftedExp_integrableOn
    (hpThetaJensenKernelTailAmplitude 1) (hpThetaJensenKernelTailRate 1 - 4) 1 hk
  have hbound :
      (∫ u : ℝ in Set.Ioi 1, u ^ 4 * hpRiemannThetaDifferentialKernel u) ≤
        ∫ u : ℝ in Set.Ioi 1, hpThetaJensenKernelTailAmplitude 1 *
          Real.exp (-(hpThetaJensenKernelTailRate 1 - 4) * (u - 1)) := by
    apply integral_mono_ae hint hmajor
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact hpThetaJensen_fourthIntegrand_le_tailEnvelope u (le_of_lt hu)
  rw [hpThetaJensen_shiftedExp_integral _ _ _ hk] at hbound
  exact hbound

#print axioms hpThetaJensen_shiftedExp_integrableOn
#print axioms hpThetaJensen_shiftedExp_integral
#print axioms hpThetaJensenKernelTailRate_one_gt_four
#print axioms hpThetaJensen_fourthPower_le_shiftedExp
#print axioms hpThetaJensen_fourthIntegrand_le_tailEnvelope
#print axioms hpThetaJensenZeroTailUpper_pos
#print axioms hpThetaJensenFourthTailUpper_pos
#print axioms hpThetaJensen_zeroMoment_tail_le
#print axioms hpThetaJensen_fourthMoment_tail_le

end HodgeProofHP
