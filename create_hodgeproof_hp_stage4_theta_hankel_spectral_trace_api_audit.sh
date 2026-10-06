#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelSpectralValues

target="HodgeProofHP/Stage4ThetaHankelSpectralTraceApiAudit.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelSpectralValues
import HodgeProofHP.Stage4ThetaHankelDiagonalEnergy
import HodgeProofHP.Stage4ThetaHankelBasisTrace

namespace HodgeProofHP

#check HPThetaHankelSpectralIndex
#check hpThetaHankelSpectralBasis
#check hpThetaHankelSpectralValue_re_eq_energy

#check hpThetaHankelBasis_norm_sq_hasSum_energy
#check hpThetaHankelAdjointSquare_diagonal_hasSum_energy
#check hpThetaHankelBasisTrace_adjointSquare_hasSum

#print axioms hpThetaHankelBasis_norm_sq_hasSum_energy
#print axioms hpThetaHankelBasisTrace_adjointSquare_hasSum
#print axioms hpThetaHankelSpectralValue_re_eq_energy

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelSpectralTraceApiAudit

python - <<'PY'
from pathlib import Path
import re

queries = {
    "Stage4ThetaHankelCountableBasis.lean": [
        "hpThetaHankelBasisSet_countable",
        "hpThetaHankelChosenBasis_norm_sq_hasSum_energy",
    ],
    "Stage4ThetaHankelDiagonalEnergy.lean": [
        "hpThetaHankelBasis_norm_sq_hasSum_energy",
    ],
}

for filename, names in queries.items():
    path = Path("HodgeProofHP") / filename
    lines = path.read_text(encoding="utf-8").splitlines()
    for name in names:
        matches = [
            i for i, line in enumerate(lines)
            if re.search(r"\b(?:theorem|lemma)\s+" + re.escape(name) + r"\b", line)
        ]
        if len(matches) != 1:
            raise SystemExit(f"STOP: {path}: expected one declaration of {name}")
        start = matches[0]
        print(f"\nSOURCE: {path}: {name}")
        for line in lines[start:start + 28]:
            print(line)
PY

printf '%s\n' 'PASS: Stage4ThetaHankelSpectralTraceApiAudit'
