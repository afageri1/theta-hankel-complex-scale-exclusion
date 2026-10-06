import HodgeProofHP.Stage4ThetaHankelSpectralBounds
import HodgeProofHP.Stage4ThetaTraceEnergyCertificate

/-!
Positive trace energy implies that S = A* A is nonzero.
Compact self-adjoint spectral theory then supplies
a strictly positive eigenvalue and a nonzero eigenvector.
-/

namespace HodgeProofHP

theorem hpThetaHankelAdjointSquare_ne_zero :
    hpThetaHankelAdjointSquare ≠ 0 := by
  intro hS
  have hA : hpThetaHankelOperator = 0 := by
    apply ContinuousLinearMap.ext
    intro f
    change hpThetaHankelOperator f = 0
    apply (hpThetaHankelAdjointSquare_apply_eq_zero_iff f).mp
    rw [hS]
    rfl
  have henergy : hpThetaFirstTraceEnergy = 0 := by
    have h :=
      hpThetaHankelChosenBasis_norm_sq_hasSum_energy.tsum_eq
    simpa [hA] using h.symm
  have hpositive :=
    hpThetaFirstTraceEnergy_gt_seven_hundredths
  linarith

theorem hpThetaHankelAdjointSquare_exists_positive_eigenvalue :
    ∃ ev : ℂ,
      Module.End.HasEigenvalue
        hpThetaHankelAdjointSquare.toLinearMap ev ∧
      ev.im = 0 ∧ 0 < ev.re := by
  classical
  by_contra hnone
  apply hpThetaHankelAdjointSquare_ne_zero
  apply
    (ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero
      hpThetaHankelAdjointSquare_isCompact
      hpThetaHankelAdjointSquare_isSymmetric).mp
  intro ev hEig
  by_contra hev
  have hspec :
      ev ∈ spectrum ℂ hpThetaHankelAdjointSquare :=
    (hpThetaHankelAdjointSquare_isCompact.hasEigenvalue_iff_mem_spectrum
      hev).mp hEig
  have hreal :=
    (hpThetaHankelAdjointSquare_spectrum_real_nonneg ev hspec).1
  have hpositive :=
    hpThetaHankelAdjointSquare_nonzero_spectrum_re_pos
      ev hev hspec
  exact hnone ⟨ev, hEig, hreal, hpositive⟩

theorem hpThetaHankelAdjointSquare_exists_positive_eigenvector :
    ∃ (ev : ℂ) (f : HPThetaHankelSpace),
      f ≠ 0 ∧
      hpThetaHankelAdjointSquare f = ev • f ∧
      ev.im = 0 ∧ 0 < ev.re := by
  obtain ⟨ev, hEig, hreal, hpositive⟩ :=
    hpThetaHankelAdjointSquare_exists_positive_eigenvalue
  obtain ⟨f, hf⟩ := hEig.exists_hasEigenvector
  have hfzero : f ≠ 0 :=
    (Module.End.hasEigenvector_iff.mp hf).2
  exact ⟨ev, f, hfzero, hf.apply_eq_smul, hreal, hpositive⟩

#print axioms hpThetaHankelAdjointSquare_ne_zero
#print axioms hpThetaHankelAdjointSquare_exists_positive_eigenvalue
#print axioms hpThetaHankelAdjointSquare_exists_positive_eigenvector

end HodgeProofHP
