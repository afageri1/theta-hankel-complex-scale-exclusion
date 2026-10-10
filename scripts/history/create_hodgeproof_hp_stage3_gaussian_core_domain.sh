#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3GaussianCoreDomain.lean <<'LEAN'
import HodgeProofHP.Stage3ComplexGaussianSchwartz
import HodgeProofHP.Stage3HarmonicCoreSpec

/-!
The Schwartz realization of the complex Gaussian belongs to the
harmonic core operator's domain.
-/

namespace HodgeProofHP

theorem hpComplexGaussianSchwartz_mem_harmonic_domain :
    (hpSchwartzCoreEquiv hpComplexGaussianSchwartz : HPSpace) ∈
      HPHarmonicCoreOperator.domain := by
  rw [hpHarmonicCoreOperator_domain_eq]
  exact (hpSchwartzCoreEquiv hpComplexGaussianSchwartz).property

#print axioms hpComplexGaussianSchwartz_mem_harmonic_domain

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3GaussianCoreDomain.lean
lake build HodgeProofHP.Stage3GaussianCoreDomain
