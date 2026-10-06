import HodgeProofHP.Stage4ThetaPhiMomentIntegrability

/-!
Audit the established differential-kernel representation and
moment-integrability frontier before differentiation under the integral.
-/

namespace HodgeProofHP

#check hpRiemannXiCritical_eq_differentialKernel_cosine_integral
#check hpThetaPhi_exp_weighted_integrableOn
#check hpThetaPhi_integrableOn
#check hpThetaPhi_secondMoment_integrableOn

#print hpRiemannXiCritical
#print hpThetaPhiMomentTwo

#print axioms hpRiemannXiCritical_eq_differentialKernel_cosine_integral
#print axioms hpThetaPhi_secondMoment_integrableOn

end HodgeProofHP
