import HodgeProofHP.Stage4ThetaFirstTraceObstruction
import HodgeProofHP.Stage4ThetaHankelSelfAdjoint

/-!
Audit of the established Hankel operator and scalar obstruction.
Operator trace and Hilbert-Schmidt identities remain to be proved.
-/

namespace HodgeProofHP

#check HPThetaHankelSpace
#check hpThetaHankelOperator
#check hpThetaHankelOperator.adjoint
#check hpThetaHankelOperator.adjoint.comp hpThetaHankelOperator
#check hpThetaHankelOperator_isSelfAdjoint

#check hpThetaHankelKernel_memLp
#check hpThetaHankelKernel_sq_lintegral_weight_identity
#check hpThetaHankelKernel_norm_sq_integrable

#check hpThetaFirstTraceEnergy
#check hpThetaXiMomentRatio
#check hpThetaFirstTraceEnergy_ne_momentRatio
#check hpThetaFirstTraceEnergy_ne_xi_secondDeriv_ratio

#print axioms hpThetaHankelOperator
#print axioms hpThetaHankelOperator_isSelfAdjoint
#print axioms hpThetaFirstTraceEnergy_ne_xi_secondDeriv_ratio

end HodgeProofHP
