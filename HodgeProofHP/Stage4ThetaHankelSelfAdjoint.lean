import HodgeProofHP.Stage4ThetaHankelPairingFormula
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
Self-adjointness of the bounded theta Hankel operator,
using the Hermitian kernel and the integrable pairing.
-/

noncomputable section

namespace HodgeProofHP

open MeasureTheory
open scoped ENNReal

theorem hpThetaHankelOperator_inner_left_eq_swapped
    (f g : HPThetaHankelSpace) :
    inner ℂ (hpThetaHankelOperator f) g =
      ∫ y, ∫ x,
        hpThetaHankelKernel x y * (star (f x) * g y)
        ∂hpThetaHankelMeasure ∂hpThetaHankelMeasure := by
  calc
    inner ℂ (hpThetaHankelOperator f) g =
        (starRingEnd ℂ)
          (inner ℂ g (hpThetaHankelOperator f)) := by
      simp only [inner_conj_symm]
    _ = (starRingEnd ℂ)
        (∫ y, ∫ x,
          hpThetaHankelKernel y x * (star (g y) * f x)
          ∂hpThetaHankelMeasure ∂hpThetaHankelMeasure) :=
      congrArg (starRingEnd ℂ)
        (hpThetaHankelOperator_inner_eq_iterated g f)
    _ = ∫ y, ∫ x,
          (starRingEnd ℂ)
            (hpThetaHankelKernel y x * (star (g y) * f x))
          ∂hpThetaHankelMeasure ∂hpThetaHankelMeasure := by
      rw [← integral_conj]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by
        exact integral_conj.symm)
    _ = ∫ y, ∫ x,
          hpThetaHankelKernel x y * (star (f x) * g y)
          ∂hpThetaHankelMeasure ∂hpThetaHankelMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by
          change
            star (hpThetaHankelKernel y x * (star (g y) * f x)) =
              hpThetaHankelKernel x y * (star (f x) * g y)
          simp only [star_mul, star_star,
            hpThetaHankelKernel_hermitian]
          ring))

theorem hpThetaHankelOperator_inner_swap
    (f g : HPThetaHankelSpace) :
    inner ℂ f (hpThetaHankelOperator g) =
      inner ℂ (hpThetaHankelOperator f) g := by
  exact
    (hpThetaHankelOperator_inner_eq_swapped f g).trans
      (hpThetaHankelOperator_inner_left_eq_swapped f g).symm

theorem hpThetaHankelOperator_isSymmetric :
    (hpThetaHankelOperator :
      HPThetaHankelSpace →ₗ[ℂ] HPThetaHankelSpace).IsSymmetric := by
  intro f g
  exact (hpThetaHankelOperator_inner_swap f g).symm

theorem hpThetaHankelOperator_isSelfAdjoint :
    IsSelfAdjoint hpThetaHankelOperator := by
  exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    hpThetaHankelOperator_isSymmetric

#print axioms hpThetaHankelOperator_inner_left_eq_swapped
#print axioms hpThetaHankelOperator_inner_swap
#print axioms hpThetaHankelOperator_isSymmetric
#print axioms hpThetaHankelOperator_isSelfAdjoint

end HodgeProofHP
