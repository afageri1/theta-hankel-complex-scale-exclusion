#!/usr/bin/env bash
set -euo pipefail

cat > HodgeProofHP/Stage3SelfAdjointApiAudit.lean <<'LEAN'
import HodgeProofHP.Stage3ClosureLeAdjoint

/-!
API audit for the remaining self-adjointness problem.
This file asserts no self-adjointness theorem.
-/

namespace HodgeProofHP

#check HPHarmonicClosure
#check hpHarmonicClosure_le_core_adjoint
#check hpHarmonicClosure_domain_dense
#check hpHarmonicCoreOperator_isFormalAdjoint

#check LinearPMap.isSelfAdjoint_def
#check LinearPMap.mem_adjoint_domain_iff
#check LinearPMap.adjoint_apply_eq
#check LinearPMap.adjoint_isClosed
#check LinearPMap.IsFormalAdjoint.le_adjoint

#check (HPHarmonicClosure.adjoint = HPHarmonicClosure)
#check (HPHarmonicCoreOperator.adjoint.domain ≤
  HPHarmonicClosure.domain)

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage3SelfAdjointApiAudit.lean
lake build HodgeProofHP.Stage3SelfAdjointApiAudit
