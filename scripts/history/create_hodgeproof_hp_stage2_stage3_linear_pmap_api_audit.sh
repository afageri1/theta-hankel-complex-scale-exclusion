#!/usr/bin/env bash
set -euo pipefail

source_file="HodgeProofHP/Stage2MultiplicationDomainSubmodule.lean"
audit_file="HodgeProofHP/Stage2MultiplicationLinearPMapApiAudit.lean"

if [[ ! -f "$source_file" ]]; then
  echo "STOP: run this from the hodgeproof-hp repository root."
  exit 1
fi

if [[ -e "$audit_file" ]]; then
  echo "STOP: audit file already exists; inspect it before replacing anything."
  exit 1
fi

cat > "$audit_file" <<'LEAN'
import HodgeProofHP.Stage2MultiplicationDomainSubmodule

/-! HP.2.3 API audit for the coordinate multiplication partial linear map. -/

namespace HodgeProofHP

#check HPSpace
#check HPMultiplicationDomain
#check HPMultiplicationDomainPredicate
#check hpCoordinateMulRepresentative

#check LinearPMap
#print LinearPMap

#check MeasureTheory.MemLp.toLp
#check MeasureTheory.MemLp.toLp_congr
#check MeasureTheory.MemLp.toLp_add
#check MeasureTheory.MemLp.toLp_const_smul

end HodgeProofHP
LEAN

echo "=== Domain and representative definitions ==="
sed -n '1,36p' HodgeProofHP/Stage2MultiplicationDomainApiAudit.lean

echo "=== HP.2.3 API audit ==="
lake env lean "$audit_file"
lake build HodgeProofHP.Stage2MultiplicationLinearPMapApiAudit
