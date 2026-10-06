import HodgeProofHP.Stage4ThetaHankelSpectralProductSecondDerivative

/-!
The constructed spectral product cannot equal normalized Riemann Xi.

The obstruction concerns the current product and its fixed normalization.
It does not exclude modified kernels, rescaling, or additional factors.
-/

namespace HodgeProofHP

theorem hpThetaHankelSpectralProduct_secondDeriv_trace_identity :
    (deriv (deriv hpThetaHankelSpectralProduct) 0).re =
      -2 *
        (hpThetaHankelBasisTrace
          hpThetaHankelSpectralBasis
          hpThetaHankelAdjointSquare).re := by
  rw [hpThetaHankelSpectralBasisTrace_eq_energy]
  simpa only [Complex.ofReal_re] using
    hpThetaHankelSpectralProduct_secondDeriv_zero_re

theorem hpThetaHankelSpectralProduct_ne_normalizedXi :
    hpThetaHankelSpectralProduct ≠ hpThetaNormalizedXi := by
  exact hpThetaHankel_function_ne_normalizedXi_of_trace_identity
    hpThetaHankelSpectralBasis
    hpThetaHankelSpectralProduct
    hpThetaHankelSpectralProduct_secondDeriv_trace_identity

theorem hpThetaHankelSpectralProduct_exists_ne_normalizedXi :
    ∃ z : ℂ,
      hpThetaHankelSpectralProduct z ≠ hpThetaNormalizedXi z := by
  classical
  by_contra h
  apply hpThetaHankelSpectralProduct_ne_normalizedXi
  funext z
  by_contra hz
  exact h ⟨z, hz⟩

#print axioms hpThetaHankelSpectralProduct_secondDeriv_trace_identity
#print axioms hpThetaHankelSpectralProduct_ne_normalizedXi
#print axioms hpThetaHankelSpectralProduct_exists_ne_normalizedXi

end HodgeProofHP
