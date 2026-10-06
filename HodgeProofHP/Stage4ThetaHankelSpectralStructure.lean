import HodgeProofHP.Stage4ThetaHankelAdjointSquareSpectrum
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
Spectral structure of the compact self-adjoint operator S = A* A.

Nonzero eigenspaces are finite-dimensional.
The orthogonal complement of the supremum of all eigenspaces is trivial.
The latter statement includes the eigenspace at zero.
-/

namespace HodgeProofHP

theorem hpThetaHankelAdjointSquare_eigenspace_finiteDimensional
    (ev : ℂ) (hev : ev ≠ 0) :
    FiniteDimensional ℂ
      (Module.End.eigenspace
        hpThetaHankelAdjointSquare.toLinearMap ev) := by
  exact ContinuousLinearMap.finite_dimensional_eigenspace
    hpThetaHankelAdjointSquare_isCompact ev hev

theorem hpThetaHankelAdjointSquare_eigenspaces_orthogonalComplement_eq_bot :
    (⨆ ev : ℂ,
      Module.End.eigenspace
        hpThetaHankelAdjointSquare.toLinearMap ev)ᗮ = ⊥ := by
  exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    hpThetaHankelAdjointSquare_isCompact
    hpThetaHankelAdjointSquare_isSymmetric

#print axioms hpThetaHankelAdjointSquare_eigenspace_finiteDimensional
#print axioms hpThetaHankelAdjointSquare_eigenspaces_orthogonalComplement_eq_bot

end HodgeProofHP
