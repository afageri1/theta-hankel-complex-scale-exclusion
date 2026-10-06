import HodgeProofHP.Stage4ThetaHankelAdjointSquareCompact
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
Self-adjointness of the adjoint square of the theta Hankel operator.
-/

namespace HodgeProofHP

theorem hpThetaHankelAdjointSquare_adjoint_eq :
    hpThetaHankelAdjointSquare.adjoint =
      hpThetaHankelAdjointSquare := by
  unfold hpThetaHankelAdjointSquare
  rw [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

theorem hpThetaHankelAdjointSquare_isSelfAdjoint :
    IsSelfAdjoint hpThetaHankelAdjointSquare := by
  exact ContinuousLinearMap.isSelfAdjoint_iff'.mpr
    hpThetaHankelAdjointSquare_adjoint_eq

theorem hpThetaHankelAdjointSquare_isSymmetric :
    hpThetaHankelAdjointSquare.toLinearMap.IsSymmetric := by
  exact hpThetaHankelAdjointSquare_isSelfAdjoint.isSymmetric

#print axioms hpThetaHankelAdjointSquare_adjoint_eq
#print axioms hpThetaHankelAdjointSquare_isSelfAdjoint
#print axioms hpThetaHankelAdjointSquare_isSymmetric

end HodgeProofHP
