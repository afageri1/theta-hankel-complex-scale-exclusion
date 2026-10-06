import HodgeProofHP.Stage4ThetaHankelEigenspaceBases
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
Collect the Hilbert bases of the eigenspaces of A* A.
Completeness of the collected family is a separate step.
-/

namespace HodgeProofHP

noncomputable abbrev HPThetaHankelSpectralIndex :=
  Σ ev : ℂ, ↥(hpThetaHankelEigenspaceBasisSet ev)

/-- The collected vectors, viewed in the ambient Hilbert space. -/
noncomputable def hpThetaHankelSpectralFamily
    (i : HPThetaHankelSpectralIndex) : HPThetaHankelSpace :=
  (hpThetaHankelEigenspace i.1).subtypeₗᵢ
    (hpThetaHankelEigenspaceBasis i.1 i.2)

set_option maxHeartbeats 2000000 in
theorem hpThetaHankelSpectralFamily_orthonormal :
    Orthonormal ℂ hpThetaHankelSpectralFamily := by
  exact OrthogonalFamily.orthonormal_sigma_orthonormal
    (𝕜 := ℂ)
    (E := HPThetaHankelSpace)
    (ι := ℂ)
    (G := fun ev => ↥(hpThetaHankelEigenspace ev))
    (V := fun ev => (hpThetaHankelEigenspace ev).subtypeₗᵢ)
    (α := fun ev => ↥(hpThetaHankelEigenspaceBasisSet ev))
    (v_family := fun ev => ⇑(hpThetaHankelEigenspaceBasis ev))
    hpThetaHankelAdjointSquare_eigenspaces_orthogonalFamily
    (fun ev => hpThetaHankelEigenspaceBasis_orthonormal ev)

theorem hpThetaHankelSpectralFamily_mem_eigenspace
    (i : HPThetaHankelSpectralIndex) :
    hpThetaHankelSpectralFamily i ∈
      hpThetaHankelEigenspace i.1 := by
  exact (hpThetaHankelEigenspaceBasis i.1 i.2).property

theorem hpThetaHankelSpectralFamily_apply
    (i : HPThetaHankelSpectralIndex) :
    hpThetaHankelAdjointSquare
        (hpThetaHankelSpectralFamily i) =
      i.1 • hpThetaHankelSpectralFamily i := by
  exact Module.End.mem_eigenspace_iff.mp
    (hpThetaHankelSpectralFamily_mem_eigenspace i)

#print axioms hpThetaHankelSpectralFamily
#print axioms hpThetaHankelSpectralFamily_orthonormal
#print axioms hpThetaHankelSpectralFamily_mem_eigenspace
#print axioms hpThetaHankelSpectralFamily_apply

end HodgeProofHP
