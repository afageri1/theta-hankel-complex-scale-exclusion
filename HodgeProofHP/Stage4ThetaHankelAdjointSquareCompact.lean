import HodgeProofHP.Stage4ThetaHankelCompactOperator
import HodgeProofHP.Stage4ThetaHankelAdjointSquare

/-!
Compactness of the adjoint square of the theta Hankel operator.
-/

namespace HodgeProofHP

/-- The adjoint square A* A is compact because A is compact
and its adjoint is a continuous linear operator. -/
theorem hpThetaHankelAdjointSquare_isCompact :
    IsCompactOperator hpThetaHankelAdjointSquare := by
  change IsCompactOperator
    (fun x =>
      hpThetaHankelOperator.adjoint (hpThetaHankelOperator x))
  exact hpThetaHankelOperator_isCompact.clm_comp
    hpThetaHankelOperator.adjoint

#print axioms hpThetaHankelAdjointSquare_isCompact

end HodgeProofHP
