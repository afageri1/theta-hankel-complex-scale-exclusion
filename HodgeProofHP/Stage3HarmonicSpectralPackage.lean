import HodgeProofHP.Stage3HarmonicFullSpectrum

/-!
# Verified harmonic spectral package

Collect self-adjointness, the orthonormal Hermite family, the full
spectrum, and compactness of unit imaginary resolvents.

No correspondence with the Riemann Xi function is asserted here.
-/

noncomputable section

namespace HodgeProofHP

theorem hpHarmonic_spectral_package :
    HPHarmonicClosure.adjoint = HPHarmonicClosure ∧
    Orthonormal ℂ hpHermiteNormalizedL2 ∧
    hpHarmonicClosureSpectrum =
      Set.range (fun n : ℕ => 2 * (n : ℂ) + 1) ∧
    (∀ (c : ℂ) (hcIm : c.im ≠ 0) (hcRe : c.re = 0)
        (hcNorm : ‖c‖ = 1),
      IsCompactOperator
        (hpHarmonicUnitImaginaryResolvent c hcIm hcRe hcNorm)) := by
  refine ⟨hpHarmonicClosure_adjoint_eq_self,
    hpHermiteNormalizedL2_orthonormal,
    hpHarmonicClosure_spectrum_eq_hermite_range, ?_⟩
  intro c hcIm hcRe hcNorm
  exact hpHarmonicUnitImaginaryResolvent_isCompact c hcIm hcRe hcNorm

end HodgeProofHP

#check HodgeProofHP.hpHermiteHilbertBasis
#check HodgeProofHP.hpHarmonicGeneralResolvent
#check HodgeProofHP.hpHarmonicGeneralSolution_equation
#check HodgeProofHP.hpHarmonicGeneralResolvent_left_inverse
#check HodgeProofHP.hpHarmonicGeneralResolvent_isCompact
#print axioms HodgeProofHP.hpHarmonic_spectral_package
