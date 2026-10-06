import HodgeProofHP.Stage4ThetaHankelChosenDiagonalAbsolute

/-!
Audit the established summability input for finite-rank approximation.
Compactness is not asserted in this module.
-/

namespace HodgeProofHP

example :
    Summable
      (fun i : hpThetaHankelBasisSet =>
        ‖hpThetaHankelOperator
          (hpThetaHankelHilbertBasis i)‖ ^ 2) :=
  hpThetaHankelChosenBasis_norm_sq_hasSum_energy.summable

#check hpThetaHankelOperator
#check hpThetaHankelHilbertBasis
#check hpThetaHankelBasisSet_countable
#check hpThetaHankelChosenBasis_norm_sq_hasSum_energy
#check hpThetaHankelChosenDiagonal_norm_summable

#print axioms hpThetaHankelChosenBasis_norm_sq_hasSum_energy
#print axioms hpThetaHankelChosenDiagonal_norm_summable

end HodgeProofHP
