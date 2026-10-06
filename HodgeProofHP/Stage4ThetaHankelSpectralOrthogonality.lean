import HodgeProofHP.Stage4ThetaHankelSpectralStructure

/-!
Orthogonality of eigenspaces and strict positivity
of nonzero spectral values of S = A* A.
-/

namespace HodgeProofHP

theorem hpThetaHankelAdjointSquare_eigenspaces_orthogonalFamily :
    OrthogonalFamily ℂ
      (fun ev : ℂ =>
        ↥(Module.End.eigenspace
          hpThetaHankelAdjointSquare.toLinearMap ev))
      (fun ev : ℂ =>
        (Module.End.eigenspace
          hpThetaHankelAdjointSquare.toLinearMap ev).subtypeₗᵢ) := by
  exact
    hpThetaHankelAdjointSquare_isSymmetric.orthogonalFamily_eigenspaces

theorem hpThetaHankelAdjointSquare_spectralValue_eq_cast_re
    (ev : ℂ)
    (hspec : ev ∈ spectrum ℂ hpThetaHankelAdjointSquare) :
    ev = (ev.re : ℂ) := by
  have hreal :=
    (hpThetaHankelAdjointSquare_spectrum_real_nonneg ev hspec).1
  apply Complex.ext
  · simp
  · simpa using hreal

theorem hpThetaHankelAdjointSquare_nonzero_spectrum_re_pos
    (ev : ℂ) (hev : ev ≠ 0)
    (hspec : ev ∈ spectrum ℂ hpThetaHankelAdjointSquare) :
    0 < ev.re := by
  obtain ⟨hreal, hnonneg⟩ :=
    hpThetaHankelAdjointSquare_spectrum_real_nonneg ev hspec
  have hne : ev.re ≠ 0 := by
    intro hzero
    apply hev
    apply Complex.ext
    · simpa using hzero
    · simpa using hreal
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

#print axioms hpThetaHankelAdjointSquare_eigenspaces_orthogonalFamily
#print axioms hpThetaHankelAdjointSquare_spectralValue_eq_cast_re
#print axioms hpThetaHankelAdjointSquare_nonzero_spectrum_re_pos

end HodgeProofHP
