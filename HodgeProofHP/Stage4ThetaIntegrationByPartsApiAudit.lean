import HodgeProofHP.Stage4ThetaProfileZeroBoundary

/-!
Audit the project interfaces needed for finite-interval integration
by parts in the differential theta-kernel representation.
No integration-by-parts identity is asserted in this module.
-/

namespace HodgeProofHP

-- Profile derivatives and their regularity.
#check hpRiemannThetaLogProfile_hasDerivAt
#check hpRiemannThetaLogProfile_first_hasDerivAt
#check hpRiemannThetaLogProfile_continuous
#check hpRiemannThetaLogProfile_deriv_continuous
#check hpRiemannThetaLogProfile_deriv_differentiable
#check hpRiemannThetaLogProfile_secondDeriv_function

-- Exact differential-kernel normalization.
#print hpRiemannThetaDifferentialKernel

-- Verified lower-boundary value.
#check hpRiemannThetaLogProfile_deriv_zero
#print axioms hpRiemannThetaLogProfile_deriv_zero

-- Integrability interfaces: print hypotheses, not proof terms.
#check hpRiemannThetaLogProfile_cos_integrableOn
#check hpRiemannThetaLogProfile_deriv_sin_integrableOn

-- Existing cosine representation to be transformed.
#check hpRiemannXiCritical_eq_logProfile_cosine_integral

end HodgeProofHP
