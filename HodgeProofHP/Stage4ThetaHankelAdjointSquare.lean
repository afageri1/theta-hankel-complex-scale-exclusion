import HodgeProofHP.Stage4ThetaHankelTraceApiAudit

/-!
The adjoint square of the established theta Hankel operator.
Its trace-class property and trace-energy identity remain separate goals.
-/

namespace HodgeProofHP

/-- The bounded operator A* A associated with the theta Hankel operator. -/
noncomputable def hpThetaHankelAdjointSquare :
    HPThetaHankelSpace →L[ℂ] HPThetaHankelSpace :=
  hpThetaHankelOperator.adjoint.comp hpThetaHankelOperator

theorem hpThetaHankelAdjointSquare_apply
    (f : HPThetaHankelSpace) :
    hpThetaHankelAdjointSquare f =
      hpThetaHankelOperator.adjoint (hpThetaHankelOperator f) := by
  rfl

#check hpThetaHankelAdjointSquare
#print axioms hpThetaHankelAdjointSquare
#print axioms hpThetaHankelAdjointSquare_apply

end HodgeProofHP
