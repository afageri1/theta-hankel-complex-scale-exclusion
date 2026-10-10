#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3GaussianL2Domain.lean <<'LEAN'
import HodgeProofHP.Stage3GaussianL2Identification

/-!
The existing Gaussian L² element belongs to the harmonic
core operator's domain.
-/

namespace HodgeProofHP

theorem hpGaussianGroundL2_mem_harmonic_domain :
    hpGaussianGroundL2 ∈ HPHarmonicCoreOperator.domain := by
  rw [hpGaussianGroundL2_eq_schwartz,
    hpHarmonicCoreOperator_domain_eq]
  exact ⟨hpComplexGaussianSchwartz, rfl⟩

#print axioms hpGaussianGroundL2_mem_harmonic_domain

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3GaussianL2Domain.lean
lake build HodgeProofHP.Stage3GaussianL2Domain
