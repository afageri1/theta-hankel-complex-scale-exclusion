import HodgeProofHP.Stage4ThetaHankelBoundedOperator
import Mathlib.MeasureTheory.Integral.Prod

/-!
Product-space integrability of the Hankel pairing,
and the resulting Fubini identity.
-/

noncomputable section

namespace HodgeProofHP

open MeasureTheory
open scoped ENNReal

theorem hpThetaHankelPairingTensor_memLp
    (f g : HPThetaHankelSpace) :
    MemLp (fun p : ℝ × ℝ => star (f p.1) * g p.2) 2
      (hpThetaHankelMeasure.prod hpThetaHankelMeasure) := by
  have hf :
      AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1)
        (hpThetaHankelMeasure.prod hpThetaHankelMeasure) :=
    (Lp.memLp f).aestronglyMeasurable.comp_fst
  have hg :
      AEStronglyMeasurable (fun p : ℝ × ℝ => g p.2)
        (hpThetaHankelMeasure.prod hpThetaHankelMeasure) :=
    (Lp.memLp g).aestronglyMeasurable.comp_snd
  have hmeas :
      AEStronglyMeasurable
        (fun p : ℝ × ℝ => star (f p.1) * g p.2)
        (hpThetaHankelMeasure.prod hpThetaHankelMeasure) := by
    have h := hf.star.mul hg
    have heq :
        ((star (fun p : ℝ × ℝ => f p.1)) *
          (fun p : ℝ × ℝ => g p.2)) =
        (fun p : ℝ × ℝ => star (f p.1) * g p.2) := by
      funext p
      rfl
    rw [heq] at h
    exact h
  have hfi :
      Integrable (fun x => ‖f x‖ ^ 2) hpThetaHankelMeasure :=
    (memLp_two_iff_integrable_sq_norm
      (Lp.memLp f).aestronglyMeasurable).1 (Lp.memLp f)
  have hgi :
      Integrable (fun y => ‖g y‖ ^ 2) hpThetaHankelMeasure :=
    (memLp_two_iff_integrable_sq_norm
      (Lp.memLp g).aestronglyMeasurable).1 (Lp.memLp g)
  apply (memLp_two_iff_integrable_sq_norm hmeas).2
  have heq :
      (fun p : ℝ × ℝ => ‖star (f p.1) * g p.2‖ ^ 2) =
        (fun p : ℝ × ℝ => ‖f p.1‖ ^ 2 * ‖g p.2‖ ^ 2) := by
    funext p
    simp only [norm_mul, norm_star, mul_pow]
  rw [heq]
  exact hfi.mul_prod hgi

theorem hpThetaHankelPairing_integrable
    (f g : HPThetaHankelSpace) :
    Integrable
      (fun p : ℝ × ℝ =>
        hpThetaHankelKernel p.1 p.2 * (star (f p.1) * g p.2))
      (hpThetaHankelMeasure.prod hpThetaHankelMeasure) := by
  have h :=
    MemLp.integrable_mul (p := 2) (q := 2)
      hpThetaHankelKernel_memLp
      (hpThetaHankelPairingTensor_memLp f g)
  have heq :
      ((fun p : ℝ × ℝ => hpThetaHankelKernel p.1 p.2) *
        (fun p : ℝ × ℝ => star (f p.1) * g p.2)) =
      (fun p : ℝ × ℝ =>
        hpThetaHankelKernel p.1 p.2 * (star (f p.1) * g p.2)) := by
    funext p
    rfl
  rw [heq] at h
  exact h

theorem hpThetaHankelPairing_integral_swap
    (f g : HPThetaHankelSpace) :
    (∫ x, ∫ y,
      hpThetaHankelKernel x y * (star (f x) * g y)
        ∂hpThetaHankelMeasure ∂hpThetaHankelMeasure) =
    ∫ y, ∫ x,
      hpThetaHankelKernel x y * (star (f x) * g y)
        ∂hpThetaHankelMeasure ∂hpThetaHankelMeasure := by
  exact integral_integral_swap (hpThetaHankelPairing_integrable f g)

#print axioms hpThetaHankelPairingTensor_memLp
#print axioms hpThetaHankelPairing_integrable
#print axioms hpThetaHankelPairing_integral_swap

end HodgeProofHP
