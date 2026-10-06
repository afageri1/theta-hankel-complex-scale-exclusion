import HodgeProofHP.Stage4ThetaNormalizedXiObstruction
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
An actual Hilbert basis for the Hankel space.

The index set is not yet proved countable.
No separability assumption is introduced.
-/

namespace HodgeProofHP

theorem hpThetaHankel_exists_hilbertBasis :
    ∃ (w : Set HPThetaHankelSpace)
      (b : HilbertBasis w ℂ HPThetaHankelSpace),
      ⇑b = ((↑) : w → HPThetaHankelSpace) := by
  exact exists_hilbertBasis ℂ HPThetaHankelSpace

noncomputable def hpThetaHankelBasisSet :
    Set HPThetaHankelSpace :=
  hpThetaHankel_exists_hilbertBasis.choose

noncomputable def hpThetaHankelHilbertBasis :
    HilbertBasis hpThetaHankelBasisSet ℂ HPThetaHankelSpace :=
  hpThetaHankel_exists_hilbertBasis.choose_spec.choose

theorem hpThetaHankelHilbertBasis_coe :
    ⇑hpThetaHankelHilbertBasis =
      ((↑) : hpThetaHankelBasisSet → HPThetaHankelSpace) := by
  exact hpThetaHankel_exists_hilbertBasis.choose_spec.choose_spec

theorem hpThetaHankelHilbertBasis_orthonormal :
    Orthonormal ℂ
      (hpThetaHankelHilbertBasis :
        hpThetaHankelBasisSet → HPThetaHankelSpace) := by
  exact hpThetaHankelHilbertBasis.orthonormal

#print axioms hpThetaHankel_exists_hilbertBasis
#print axioms hpThetaHankelHilbertBasis
#print axioms hpThetaHankelHilbertBasis_coe
#print axioms hpThetaHankelHilbertBasis_orthonormal

end HodgeProofHP
