#!/usr/bin/env bash
set -euo pipefail

if [[ ! -f lakefile.lean && ! -f lakefile.toml ]]; then
  echo "Run from ~/hodgeproof-hp"
  exit 1
fi

lake build HodgeProofHP.Stage4ThetaPhiMomentIntegrability

target="HodgeProofHP/Stage4ThetaPhiDerivativeApiAudit.lean"
mkdir -p HodgeProofHP

if [[ -f "$target" ]]; then
  cp "$target" \
    "${target}.before_update_$(date +%Y%m%d_%H%M%S)_$$"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaPhiMomentIntegrability

/-!
Audit the established differential-kernel representation and
moment-integrability frontier before differentiation under the integral.
-/

namespace HodgeProofHP

#check hpRiemannXiCritical_eq_differentialKernel_cosine_integral
#check hpThetaPhi_exp_weighted_integrableOn
#check hpThetaPhi_integrableOn
#check hpThetaPhi_secondMoment_integrableOn

#print hpRiemannXiCritical
#print hpThetaPhiMomentTwo

#print axioms hpRiemannXiCritical_eq_differentialKernel_cosine_integral
#print axioms hpThetaPhi_secondMoment_integrableOn

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaPhiDerivativeApiAudit

python - <<'PY'
from pathlib import Path
import re

root = Path(".lake/packages/mathlib/Mathlib")
if not root.is_dir():
    raise SystemExit("STOP: mathlib source directory not found")

patterns = (
    "hasDerivAt_integral",
    "hasFDerivAt_integral",
    "differentiableAt_integral",
    "deriv_integral",
)

matches = []
for path in sorted(root.rglob("*.lean")):
    source = path.read_text(encoding="utf-8")
    lines = source.splitlines()
    for i, line in enumerate(lines):
        if not re.match(
            r"^\s*(?:(?:protected|private|noncomputable)\s+)*"
            r"(?:theorem|lemma|def)\s+", line
        ):
            continue
        if not any(p.lower() in line.lower() for p in patterns):
            continue
        matches.append((path, i, lines))

if not matches:
    raise SystemExit(
        "STOP: no matching declarations; send this audit output"
    )

print("\n=== Installed differentiation-under-integral APIs ===")
for path, i, lines in matches:
    print(f"\nSOURCE: {path.as_posix()}:{i + 1}")
    for j in range(i, min(i + 55, len(lines))):
        text = lines[j]
        print(text)
        if ":=" in text:
            break

print(f"\nFOUND: {len(matches)} declarations")
PY

echo "PASS: Stage4ThetaPhiDerivativeApiAudit"
