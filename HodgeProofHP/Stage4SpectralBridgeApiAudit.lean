import HodgeProofHP.Stage3HarmonicSpectralPackage
import HodgeProofHP.Stage4RiemannXiNontrivialZeros

/-!
# Spectral bridge API audit

The harmonic spectral package and the xi zero criteria are established
separately. This module inspects their interfaces.
It does not assert a correspondence between harmonic eigenvalues
and Riemann xi zeros.
-/

namespace HodgeProofHP

-- Operator and domain interfaces.
#check HPHarmonicClosure
#check HPHarmonicClosure.domain
#check HPHarmonicClosure.toFun
#check hpHarmonicClosure_isSelfAdjoint
#check hpHarmonicClosure_no_nonreal_eigen

-- Established harmonic spectrum.
#check hpHermite_closure_eigenvector_exists
#check hpHarmonicClosure_mem_spectrum_iff
#check hpHarmonicClosure_spectrum_eq_hermite_range
#check hpHarmonic_spectral_package

-- Actual analytic target.
#print hpRiemannXiCritical
#check hpRiemannXiCritical_zero_im_bounds
#check hpRiemannHypothesis_iff_critical_real_zeros

end HodgeProofHP

#print axioms HodgeProofHP.hpHarmonic_spectral_package
#print axioms HodgeProofHP.hpHarmonicClosure_no_nonreal_eigen
#print axioms HodgeProofHP.hpRiemannHypothesis_iff_critical_real_zeros
