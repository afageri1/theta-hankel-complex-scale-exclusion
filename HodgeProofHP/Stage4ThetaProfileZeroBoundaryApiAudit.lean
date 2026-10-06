import HodgeProofHP.Stage4ThetaTrigonometricIntegrability

/-!
Audit the definitions and derivative APIs needed to compute the
theta logarithmic profile's boundary derivative at zero.
This module does not assert the boundary derivative identity.
-/

namespace HodgeProofHP

-- Exact normalization and reflection identity.
#print hpRiemannThetaKernel
#print hpRiemannThetaKernel_transformation
#print hpRiemannThetaLogProfile

-- Existing derivative and continuity results.
#check hpRiemannThetaLogProfile_hasDerivAt
#print hpRiemannThetaLogProfile_deriv_function
#check hpRiemannThetaLogProfile_continuous
#check hpRiemannThetaLogProfile_deriv_continuous

-- Calculus interfaces for differentiating a reflected identity.
#check HasDerivAt.comp
#check HasDerivAt.mul
#check HasDerivAt.sub
#check HasDerivAt.deriv

-- Trust checks for the existing ingredients.
#print axioms hpRiemannThetaKernel_transformation
#print axioms hpRiemannThetaLogProfile_hasDerivAt
#print axioms hpRiemannThetaLogProfile_deriv_continuous

end HodgeProofHP
