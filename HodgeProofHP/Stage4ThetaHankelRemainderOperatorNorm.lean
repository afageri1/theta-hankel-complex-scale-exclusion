import HodgeProofHP.Stage4ThetaHankelRemainderBound
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Operator-norm bounds for the finite Hankel approximation error.
-/

namespace HodgeProofHP

theorem hpThetaHankelOperator_sub_apply_norm_le
    (F : Finset hpThetaHankelBasisSet)
    (x : HPThetaHankelSpace) :
    ‖(hpThetaHankelOperator -
        hpThetaHankelFiniteApproximation F) x‖ ≤
      Real.sqrt (hpThetaHankelTailEnergy F) * ‖x‖ := by
  have hbound :=
    hpThetaHankelOperator_sub_apply_norm_sq_le F x
  have henergy : 0 ≤ hpThetaHankelTailEnergy F :=
    hpThetaHankelTailEnergy_nonneg F
  have hproduct_nonneg :
      0 ≤ Real.sqrt (hpThetaHankelTailEnergy F) * ‖x‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x)
  have hproduct_sq :
      (Real.sqrt (hpThetaHankelTailEnergy F) * ‖x‖) ^ 2 =
        hpThetaHankelTailEnergy F * ‖x‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt henergy]
  have hnorm_nonneg :
      0 ≤ ‖(hpThetaHankelOperator -
        hpThetaHankelFiniteApproximation F) x‖ :=
    norm_nonneg _
  nlinarith only
    [hbound, hproduct_sq, hproduct_nonneg, hnorm_nonneg]

theorem hpThetaHankelOperator_sub_opNorm_le
    (F : Finset hpThetaHankelBasisSet) :
    ‖hpThetaHankelOperator -
        hpThetaHankelFiniteApproximation F‖ ≤
      Real.sqrt (hpThetaHankelTailEnergy F) := by
  exact
    (hpThetaHankelOperator -
      hpThetaHankelFiniteApproximation F).opNorm_le_bound
      (Real.sqrt_nonneg _)
      (fun x => hpThetaHankelOperator_sub_apply_norm_le F x)

#print axioms hpThetaHankelOperator_sub_apply_norm_le
#print axioms hpThetaHankelOperator_sub_opNorm_le

end HodgeProofHP
