#!/usr/bin/env bash
set -euo pipefail

lake build HodgeProofHP.Stage4ThetaHankelParsevalNorm

target="HodgeProofHP/Stage4ThetaHankelParsevalTonelliAudit.lean"

if [ -f "$target" ]; then
  cp -p "$target" "$target.before_update_$(date +%Y%m%d_%H%M%S)"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaHankelParsevalNorm

namespace HodgeProofHP

-- Pointwise action and its identification with a row inner product.
#check hpThetaHankelActionFunction
#check hpThetaHankelActionFunction_eq_inner
#check hpThetaHankelActionFunction_aestronglyMeasurable

-- Almost-everywhere square-integrable rows and row energy.
#check hpThetaHankelKernel_row_memLp_ae
#check hpThetaHankelRowL2_norm_sq
#check hpThetaHankelRowEnergy
#check hpThetaHankelRowEnergy_integrable

-- Operator representatives and their squared norms.
#check hpThetaHankelOperator_coeFn_ae
#check hpThetaHankelSpace_norm_sq_eq_integral

-- Parseval and the kernel energy identity.
#check hpThetaHankelRow_parseval_norm_tsum
#check hpThetaHankelKernel_sq_lintegral_weight_identity
#check hpThetaFirstTraceEnergy

-- Print the proofs to expose the exact conversions already used.
#print hpThetaHankelActionFunction_eq_inner
#print hpThetaHankelRowL2_norm_sq
#print hpThetaHankelSpace_norm_sq_eq_integral

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaHankelParsevalTonelliAudit

python - <<'PY'
from pathlib import Path
import re

root = Path(".lake/packages/mathlib/Mathlib")
wanted = re.compile(
    r"\b(ofReal_tsum|lintegral_tsum|"
    r"integral_eq_lintegral_of_nonneg_ae|"
    r"integral_eq_lintegral_of_nonneg|"
    r"ae_all_iff)\b"
)
declaration = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:(?:protected|private|noncomputable)\s+)*"
    r"(?:theorem|lemma|def)\s+"
)

print("=== Sum / integral / countable AE source declarations ===")
count = 0
for path in sorted(root.rglob("*.lean")):
    lines = path.read_text(encoding="utf-8").splitlines()
    for i, line in enumerate(lines):
        if declaration.search(line) and wanted.search(line):
            print(f"\n{path}:{i + 1}")
            print("\n".join(lines[i:i + 12]))
            count += 1
print(f"\nMatched declarations: {count}")
PY

printf '%s\n' 'PASS: Stage4ThetaHankelParsevalTonelliAudit'
