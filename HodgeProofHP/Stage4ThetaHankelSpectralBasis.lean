import HodgeProofHP.Stage4ThetaHankelSpectralCompleteness

/-!
A Hilbert basis of eigenvectors for the theta Hankel adjoint square.
The basis includes the zero eigenspace.
-/

namespace HodgeProofHP

/-- The collected eigenspace bases form a Hilbert basis. -/
noncomputable def hpThetaHankelSpectralBasis :
    HilbertBasis HPThetaHankelSpectralIndex ℂ HPThetaHankelSpace :=
  HilbertBasis.mkOfOrthogonalEqBot
    hpThetaHankelSpectralFamily_orthonormal
    hpThetaHankelSpectralFamily_orthogonalComplement_eq_bot

theorem hpThetaHankelSpectralBasis_coe :
    ⇑hpThetaHankelSpectralBasis = hpThetaHankelSpectralFamily := by
  exact HilbertBasis.coe_mkOfOrthogonalEqBot
    hpThetaHankelSpectralFamily_orthonormal
    hpThetaHankelSpectralFamily_orthogonalComplement_eq_bot

theorem hpThetaHankelSpectralBasis_orthonormal :
    Orthonormal ℂ ⇑hpThetaHankelSpectralBasis :=
  hpThetaHankelSpectralBasis.orthonormal

theorem hpThetaHankelSpectralBasis_apply
    (i : HPThetaHankelSpectralIndex) :
    hpThetaHankelAdjointSquare (hpThetaHankelSpectralBasis i) =
      i.1 • hpThetaHankelSpectralBasis i := by
  have hi :
      hpThetaHankelSpectralBasis i =
        hpThetaHankelSpectralFamily i :=
    congrFun hpThetaHankelSpectralBasis_coe i
  rw [hi]
  exact hpThetaHankelSpectralFamily_apply i

theorem hpThetaHankelSpectralBasis_dense_span :
    (Submodule.span ℂ
      (Set.range ⇑hpThetaHankelSpectralBasis)).topologicalClosure = ⊤ :=
  hpThetaHankelSpectralBasis.dense_span

theorem hpThetaHankelSpectralBasis_hasSum_repr
    (f : HPThetaHankelSpace) :
    HasSum
      (fun i : HPThetaHankelSpectralIndex =>
        (hpThetaHankelSpectralBasis.repr f) i •
          hpThetaHankelSpectralBasis i)
      f :=
  hpThetaHankelSpectralBasis.hasSum_repr f

#print axioms hpThetaHankelSpectralBasis
#print axioms hpThetaHankelSpectralBasis_coe
#print axioms hpThetaHankelSpectralBasis_orthonormal
#print axioms hpThetaHankelSpectralBasis_apply
#print axioms hpThetaHankelSpectralBasis_dense_span
#print axioms hpThetaHankelSpectralBasis_hasSum_repr

end HodgeProofHP
