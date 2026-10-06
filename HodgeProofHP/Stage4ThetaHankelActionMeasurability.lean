import HodgeProofHP.Stage4ThetaHankelActionIntegrability

/-!
Measurability of the Hankel action and integrability of its
row-energy function, preparatory to the L2 operator bound.
-/

noncomputable section

namespace HodgeProofHP

open MeasureTheory
open scoped ENNReal

theorem hpThetaHankelActionFunction_aestronglyMeasurable
    (f : HPThetaHankelSpace) :
    AEStronglyMeasurable
      (hpThetaHankelActionFunction f) hpThetaHankelMeasure := by
  have hf :
      AEStronglyMeasurable
        (fun p : ℝ × ℝ => f p.2)
        (hpThetaHankelMeasure.prod hpThetaHankelMeasure) :=
    (Lp.memLp f).aestronglyMeasurable.comp_snd
  have hprod :
      AEStronglyMeasurable
        (fun p : ℝ × ℝ =>
          hpThetaHankelKernel p.1 p.2 * f p.2)
        (hpThetaHankelMeasure.prod hpThetaHankelMeasure) := by
    have h :=
      hpThetaHankelKernel_continuous.aestronglyMeasurable.mul hf
    have heq :
        ((fun p : ℝ × ℝ => hpThetaHankelKernel p.1 p.2) *
          (fun p : ℝ × ℝ => f p.2)) =
        (fun p : ℝ × ℝ =>
          hpThetaHankelKernel p.1 p.2 * f p.2) := by
      funext p
      rfl
    rw [heq] at h
    exact h
  change AEStronglyMeasurable
    (fun x : ℝ =>
      ∫ y : ℝ, hpThetaHankelKernel x y * f y
        ∂hpThetaHankelMeasure)
    hpThetaHankelMeasure
  exact hprod.integral_prod_right'

def hpThetaHankelRowEnergy (x : ℝ) : ℝ :=
  ∫ y : ℝ, ‖hpThetaHankelKernel x y‖ ^ 2
    ∂hpThetaHankelMeasure

theorem hpThetaHankelRowEnergy_nonneg (x : ℝ) :
    0 ≤ hpThetaHankelRowEnergy x := by
  unfold hpThetaHankelRowEnergy
  exact integral_nonneg (fun y => sq_nonneg _)

theorem hpThetaHankelRowEnergy_integrable :
    Integrable hpThetaHankelRowEnergy hpThetaHankelMeasure := by
  have hsq :
      Integrable
        (fun p : ℝ × ℝ => ‖hpThetaHankelKernel p.1 p.2‖ ^ 2)
        (hpThetaHankelMeasure.prod hpThetaHankelMeasure) := by
    simpa only [hpThetaHankelMeasure]
      using hpThetaHankelKernel_norm_sq_integrable
  change Integrable
    (fun x : ℝ =>
      ∫ y : ℝ, ‖hpThetaHankelKernel x y‖ ^ 2
        ∂hpThetaHankelMeasure)
    hpThetaHankelMeasure
  exact hsq.integral_prod_left

#print axioms hpThetaHankelActionFunction_aestronglyMeasurable
#print axioms hpThetaHankelRowEnergy_nonneg
#print axioms hpThetaHankelRowEnergy_integrable

end HodgeProofHP
