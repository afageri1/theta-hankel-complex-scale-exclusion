#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3ClosureDomainSpec.lean <<'LEAN'
import HodgeProofHP.Stage3HarmonicClosure

/-!
The Schwartz domain is a core of the harmonic closure, whose domain is dense.
-/

namespace HodgeProofHP

theorem hpHarmonicClosure_hasSchwartzCore :
    HPHarmonicClosure.HasCore HPSchwartzDomain := by
  change HPHarmonicCoreOperator.closure.HasCore
    HPHarmonicCoreOperator.domain
  exact LinearPMap.closureHasCore HPHarmonicCoreOperator

theorem hpHarmonicClosure_domain_dense :
    Dense (HPHarmonicClosure.domain : Set HPSpace) := by
  have hsub :
      HPHarmonicCoreOperator.domain ≤ HPHarmonicClosure.domain :=
    LinearPMap.domain_mono hpHarmonicCoreOperator_le_closure
  exact hpHarmonicCoreOperator_domain_dense.mono hsub

#print axioms hpHarmonicClosure_hasSchwartzCore
#print axioms hpHarmonicClosure_domain_dense

end HodgeProofHP
LEAN

lake build HodgeProofHP.Stage3ClosureDomainSpec
