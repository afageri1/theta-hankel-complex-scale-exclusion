import HodgeProofHP.Stage4ThetaHankelTonelli
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
Translation of half-line nonnegative integrals and the interval-length
identity needed for the Hankel square-integral calculation.
-/

namespace HodgeProofHP

open MeasureTheory
open scoped ENNReal

theorem hpLIntegral_add_left_Ioi
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) (x : ℝ) :
    (∫⁻ y in Set.Ioi (0 : ℝ), F (x + y)) =
      ∫⁻ u in Set.Ioi x, F u := by
  have hpre :
      (fun y : ℝ => x + y) ⁻¹' Set.Ioi x =
        Set.Ioi (0 : ℝ) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Ioi]
    constructor
    · intro h
      linarith
    · intro h
      linarith
  have h :=
    (measurePreserving_add_left (volume : Measure ℝ) x).setLIntegral_comp_preimage
      (s := Set.Ioi x) measurableSet_Ioi hF
  simpa only [hpre] using h

theorem hpLIntegral_const_Ioo_zero
    (u : ℝ) (c : ℝ≥0∞) :
    (∫⁻ _x in Set.Ioo (0 : ℝ) u, c) =
      ENNReal.ofReal u * c := by
  rw [setLIntegral_const, Real.volume_Ioo, sub_zero, mul_comm]

theorem hpThetaPhi_sq_lintegral_add_left (x : ℝ) :
    (∫⁻ y in Set.Ioi (0 : ℝ),
      ENNReal.ofReal
        (hpRiemannThetaDifferentialKernel (x + y) ^ 2)) =
      ∫⁻ u in Set.Ioi x,
        ENNReal.ofReal
          (hpRiemannThetaDifferentialKernel u ^ 2) := by
  exact hpLIntegral_add_left_Ioi
    (fun u : ℝ =>
      ENNReal.ofReal (hpRiemannThetaDifferentialKernel u ^ 2))
    ((hpRiemannThetaDifferentialKernel_continuous.pow 2).measurable.ennreal_ofReal)
    x

theorem hpThetaHankelKernel_sq_lintegral_add_left (x : ℝ) :
    (∫⁻ y in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (‖hpThetaHankelKernel x y‖ ^ 2)) =
      ∫⁻ u in Set.Ioi x,
        ENNReal.ofReal
          (hpRiemannThetaDifferentialKernel u ^ 2) := by
  simp_rw [hpThetaHankelKernel_norm_sq]
  exact hpThetaPhi_sq_lintegral_add_left x

#print axioms hpLIntegral_add_left_Ioi
#print axioms hpLIntegral_const_Ioo_zero
#print axioms hpThetaPhi_sq_lintegral_add_left
#print axioms hpThetaHankelKernel_sq_lintegral_add_left

end HodgeProofHP
