import HodgeProofHP.Stage4ThetaHankelEigenbasisApiAudit
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
Closed eigenspaces of S = A* A and chosen Hilbert bases
inside each eigenspace, including the eigenspace at zero.
-/

namespace HodgeProofHP

noncomputable abbrev hpThetaHankelEigenspace (ev : ℂ) :
    Submodule ℂ HPThetaHankelSpace :=
  Module.End.eigenspace hpThetaHankelAdjointSquare.toLinearMap ev

theorem hpThetaHankelEigenspace_isClosed (ev : ℂ) :
    IsClosed (hpThetaHankelEigenspace ev : Set HPThetaHankelSpace) := by
  exact hpThetaHankelAdjointSquare.isClosed_eigenspace ev

instance hpThetaHankelEigenspace_completeSpace (ev : ℂ) :
    CompleteSpace ↥(hpThetaHankelEigenspace ev) := by
  letI : IsClosed
      (hpThetaHankelEigenspace ev : Set HPThetaHankelSpace) :=
    hpThetaHankelEigenspace_isClosed ev
  infer_instance

theorem hpThetaHankelEigenspace_exists_hilbertBasis (ev : ℂ) :
    ∃ (w : Set ↥(hpThetaHankelEigenspace ev))
      (b : HilbertBasis w ℂ ↥(hpThetaHankelEigenspace ev)),
      ⇑b = Subtype.val := by
  exact exists_hilbertBasis ℂ ↥(hpThetaHankelEigenspace ev)

noncomputable def hpThetaHankelEigenspaceBasisSet (ev : ℂ) :
    Set ↥(hpThetaHankelEigenspace ev) :=
  Classical.choose (hpThetaHankelEigenspace_exists_hilbertBasis ev)

noncomputable def hpThetaHankelEigenspaceBasis (ev : ℂ) :
    HilbertBasis ↥(hpThetaHankelEigenspaceBasisSet ev) ℂ
      ↥(hpThetaHankelEigenspace ev) :=
  Classical.choose
    (Classical.choose_spec
      (hpThetaHankelEigenspace_exists_hilbertBasis ev))

theorem hpThetaHankelEigenspaceBasis_coe (ev : ℂ) :
    ⇑(hpThetaHankelEigenspaceBasis ev) = Subtype.val := by
  exact Classical.choose_spec
    (Classical.choose_spec
      (hpThetaHankelEigenspace_exists_hilbertBasis ev))

theorem hpThetaHankelEigenspaceBasis_orthonormal (ev : ℂ) :
    Orthonormal ℂ ⇑(hpThetaHankelEigenspaceBasis ev) :=
  (hpThetaHankelEigenspaceBasis ev).orthonormal

#print axioms hpThetaHankelEigenspace_isClosed
#print axioms hpThetaHankelEigenspace_completeSpace
#print axioms hpThetaHankelEigenspace_exists_hilbertBasis
#print axioms hpThetaHankelEigenspaceBasis
#print axioms hpThetaHankelEigenspaceBasis_coe
#print axioms hpThetaHankelEigenspaceBasis_orthonormal

end HodgeProofHP
