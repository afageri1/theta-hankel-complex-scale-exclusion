import HodgeProofHP.Stage4ThetaHankelSeparability

/-!
Check the hypotheses needed to obtain a countable Hilbert basis.
Countability itself is not asserted in this audit.
-/

namespace HodgeProofHP

example :
    SecondCountableTopology HPThetaHankelSpace := by
  infer_instance

example :
    TopologicalSpace.SeparableSpace HPThetaHankelSpace := by
  infer_instance

example :
    Orthonormal ℂ
      (hpThetaHankelHilbertBasis :
        hpThetaHankelBasisSet → HPThetaHankelSpace) :=
  hpThetaHankelHilbertBasis_orthonormal

#check hpThetaHankelBasisSet
#check hpThetaHankelHilbertBasis
#check hpThetaHankelHilbertBasis_coe

#print axioms hpThetaHankelHilbertBasis_orthonormal

end HodgeProofHP
