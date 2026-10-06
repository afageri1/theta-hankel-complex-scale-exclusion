import HodgeProofHP.Stage4ThetaHankelSelfAdjoint

/-!
Audit of the established theta Hankel operator and its kernel.
Compact-operator APIs are inspected separately in mathlib source.
-/

namespace HodgeProofHP

#check hpThetaHankelOperator
#check hpThetaHankelOperator_isSelfAdjoint
#check hpThetaHankelKernel_memLp
#check hpThetaHankelKernel_norm_sq_integrable
#check hpThetaHankelKernel_sq_lintegral_weight_identity
#check hpThetaHankelActionL2_norm_le

#print hpThetaHankelMeasure
#print hpThetaHankelKernel
#print hpRiemannThetaDifferentialKernel
#print hpRiemannThetaLogProfile
#print hpRiemannXiCritical_eq_differentialKernel_cosine_integral

#print axioms hpThetaHankelOperator_isSelfAdjoint

end HodgeProofHP
