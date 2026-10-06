import HodgeProofHP.Stage4ThetaHankelAdjointSquareKernel
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
The spectrum of the theta Hankel adjoint square lies
on the nonnegative real axis.
No correspondence with Riemann Xi zeros is assumed.
-/

namespace HodgeProofHP

theorem hpThetaHankelAdjointSquare_mem_spectrum_exists_eigenvector
    (ev : ℂ) (hev : ev ≠ 0)
    (hspec : ev ∈ spectrum ℂ hpThetaHankelAdjointSquare) :
    ∃ f : HPThetaHankelSpace,
      f ≠ 0 ∧ hpThetaHankelAdjointSquare f = ev • f := by
  have hEig :
      Module.End.HasEigenvalue hpThetaHankelAdjointSquare.toLinearMap ev :=
    (hpThetaHankelAdjointSquare_isCompact.hasEigenvalue_iff_mem_spectrum
      hev).mpr hspec
  obtain ⟨f, hf⟩ := hEig.exists_hasEigenvector
  have hfzero : f ≠ 0 :=
    (Module.End.hasEigenvector_iff.mp hf).2
  exact ⟨f, hfzero, hf.apply_eq_smul⟩

theorem hpThetaHankelAdjointSquare_nonzero_spectrum_real_nonneg
    (ev : ℂ) (hev : ev ≠ 0)
    (hspec : ev ∈ spectrum ℂ hpThetaHankelAdjointSquare) :
    ev.im = 0 ∧ 0 ≤ ev.re := by
  obtain ⟨f, hf, heig⟩ :=
    hpThetaHankelAdjointSquare_mem_spectrum_exists_eigenvector
      ev hev hspec
  exact hpThetaHankelAdjointSquare_eigenvalue_real_nonneg
    ev f hf heig

theorem hpThetaHankelAdjointSquare_spectrum_real_nonneg
    (ev : ℂ)
    (hspec : ev ∈ spectrum ℂ hpThetaHankelAdjointSquare) :
    ev.im = 0 ∧ 0 ≤ ev.re := by
  by_cases hev : ev = 0
  · subst ev
    simp
  · exact hpThetaHankelAdjointSquare_nonzero_spectrum_real_nonneg
      ev hev hspec

#print axioms hpThetaHankelAdjointSquare_mem_spectrum_exists_eigenvector
#print axioms hpThetaHankelAdjointSquare_nonzero_spectrum_real_nonneg
#print axioms hpThetaHankelAdjointSquare_spectrum_real_nonneg

end HodgeProofHP
