#!/usr/bin/env bash
set -euo pipefail

python3 - <<'PY'
from pathlib import Path

paths = [
    Path("HodgeProofHP/Stage3AllRealGaussianDerivativeBounds.lean"),
    Path("create_hodgeproof_hp_stage3_all_real_gaussian_derivative_bounds.sh"),
]
old = "  exact hC x\n\n#print axioms hpRealGaussian_allDerivatives_weighted_bounded"
new = (
    "  simpa only [mul_assoc] using hC x\n\n"
    "#print axioms hpRealGaussian_allDerivatives_weighted_bounded"
)

updated = {}
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing {path}")
    source = path.read_text(encoding="utf-8")
    if source.count(old) != 1:
        raise SystemExit(f"STOP: expected one matching final step in {path}")
    updated[path] = source.replace(old, new)

for path, source in updated.items():
    path.write_text(source, encoding="utf-8")
    print(f"UPDATED: {path}")
PY

lake env lean HodgeProofHP/Stage3AllRealGaussianDerivativeBounds.lean
lake build HodgeProofHP.Stage3AllRealGaussianDerivativeBounds
