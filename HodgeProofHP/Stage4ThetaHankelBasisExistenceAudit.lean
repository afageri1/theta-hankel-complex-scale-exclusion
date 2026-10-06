import HodgeProofHP.Stage4ThetaNormalizedXiObstruction
import Mathlib

namespace HodgeProofHP

#check HPThetaHankelSpace
#check hpThetaHankelMeasure
#check HilbertBasis
#check hpThetaHankelBasisTrace
#check hpThetaHankelBasis_norm_sq_hasSum_energy

#synth CompleteSpace HPThetaHankelSpace
#synth InnerProductSpace ℂ HPThetaHankelSpace

-- Probe instance availability; this proves only True.
example : True := by
  first
  | haveI : SeparableSpace HPThetaHankelSpace := inferInstance
    trace "FOUND: SeparableSpace HPThetaHankelSpace"
    exact True.intro
  | trace "MISSING: automatic separability instance; an explicit proof is needed"
    exact True.intro

#print axioms hpThetaHankelBasis_norm_sq_hasSum_energy
#print axioms hpThetaHankel_function_ne_normalizedXi_of_trace_identity

end HodgeProofHP
