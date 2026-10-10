#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3HermiteFactorizationApiAudit.lean <<'LEAN'
import HodgeProofHP.Stage3HermiteFactorizationAlgebra

/-!
Definitions needed to connect the Schwartz factorization
to the harmonic operator on HPSpace.
No new factorization claim is made here.
-/

namespace HodgeProofHP

#check hpSchwartzCreation_annihilation_algebra
#check hpSchwartzCoordinateMul_apply
#check hpSchwartzSecondDeriv_apply
#check hpSchwartzQuadraticMul_apply
#check hpHarmonicCoreOperator_apply

#print hpQuadraticPotential
#print hpSchwartzSecondDeriv
#print hpSchwartzQuadraticMul
#print hpSchwartzKineticToL2
#print hpSchwartzQuadraticToL2
#print hpSchwartzHarmonicToL2

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3HermiteFactorizationApiAudit.lean
lake build HodgeProofHP.Stage3HermiteFactorizationApiAudit
