import HodgeProofHP.Stage4ThetaHankelTailEnergy

/-!
Audit of the established inputs for the operator norm remainder estimate.
No remainder estimate is asserted in this module.
-/

namespace HodgeProofHP

#check hpThetaHankelHilbertBasis
#check hpThetaHankelHilbertBasis_orthonormal
#check hpThetaHankelFiniteApproximation_apply
#check hpThetaHankelFiniteApproximation_eq_comp
#check hpThetaHankelFiniteApproximation_isCompact
#check hpThetaHankelChosenBasis_norm_sq_hasSum_energy
#check hpThetaHankelTailEnergy_tendsto_zero

#print axioms hpThetaHankelFiniteApproximation_isCompact
#print axioms hpThetaHankelTailEnergy_tendsto_zero

end HodgeProofHP
