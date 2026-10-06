#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaFirstTraceObstruction
lake build HodgeProofHP.Stage4ThetaHankelSelfAdjoint

target="HodgeProofHP/Stage4ThetaHankelTraceApiAudit.lean"
if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaFirstTraceObstruction
import HodgeProofHP.Stage4ThetaHankelSelfAdjoint

/-!
Audit of the established Hankel operator and scalar obstruction.
Operator trace and Hilbert-Schmidt identities remain to be proved.
-/

namespace HodgeProofHP

#check HPThetaHankelSpace
#check hpThetaHankelOperator
#check hpThetaHankelOperator.adjoint
#check hpThetaHankelOperator.adjoint.comp hpThetaHankelOperator
#check hpThetaHankelOperator_isSelfAdjoint

#check hpThetaHankelKernel_memLp
#check hpThetaHankelKernel_sq_lintegral_weight_identity
#check hpThetaHankelKernel_norm_sq_integrable

#check hpThetaFirstTraceEnergy
#check hpThetaXiMomentRatio
#check hpThetaFirstTraceEnergy_ne_momentRatio
#check hpThetaFirstTraceEnergy_ne_xi_secondDeriv_ratio

#print axioms hpThetaHankelOperator
#print axioms hpThetaHankelOperator_isSelfAdjoint
#print axioms hpThetaFirstTraceEnergy_ne_xi_secondDeriv_ratio

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelTraceApiAudit

mathlib=".lake/packages/mathlib/Mathlib"
if [ ! -d "$mathlib" ]; then
  printf '%s\n' "STOP: mathlib source directory not found: $mathlib"
  exit 1
fi

printf '\n%s\n' '=== Hilbert-Schmidt, trace-class and Fredholm files ==='
rg --files "$mathlib" |
  rg -i 'HilbertSchmidt|Schatten|TraceClass|Nuclear|Fredholm|Trace|IntegralOperator' ||
  true

printf '\n%s\n' '=== Relevant declarations in analysis ==='
python - "$mathlib/Analysis" <<'PY'
from pathlib import Path
import re
import sys

root = Path(sys.argv[1])
pattern = re.compile(
    r"HilbertSchmidt|hilbertSchmidt|hilbert_schmidt|"
    r"TraceClass|traceClass|trace_class|Schatten|"
    r"trace.*adjoint|adjoint.*trace|"
    r"trace.*tsum|tsum.*trace|"
    r"integralOperator|integral_operator|fredholmDet",
    re.IGNORECASE,
)
declaration = re.compile(
    r"^\s*(?:(?:noncomputable|private|protected)\s+)*"
    r"(?:def|abbrev|theorem|lemma|class|structure|instance)\b"
)

count = 0
for path in sorted(root.rglob("*.lean")):
    lines = path.read_text(encoding="utf-8").splitlines()
    for i, line in enumerate(lines):
        if declaration.match(line):
            excerpt = "\n".join(lines[i:i + 5])
            if pattern.search(excerpt):
                print(f"{path}:{i + 1}")
                print(excerpt)
                print()
                count += 1

print(f"Matched declaration excerpts: {count}")
PY

printf '%s\n' 'PASS: Stage4ThetaHankelTraceApiAudit'
