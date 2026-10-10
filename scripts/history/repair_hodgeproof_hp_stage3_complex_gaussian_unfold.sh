#!/usr/bin/env bash
set -euo pipefail

python3 - <<'PY'
from pathlib import Path

paths = [
    Path("HodgeProofHP/Stage3ComplexGaussianBound.lean"),
    Path("create_hodgeproof_hp_stage3_complex_gaussian_bound.sh"),
]
old = "    change ‖Complex.exp (-((1 / 2 : ℂ) * (x : ℂ) ^ 2))‖ = _"
new = "    unfold hpGaussianGroundFunction"

updated = {}
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing {path}")
    source = path.read_text(encoding="utf-8")
    if source.count(old) != 1:
        raise SystemExit(f"STOP: expected exactly one change line in {path}")
    updated[path] = source.replace(old, new)

for path, source in updated.items():
    path.write_text(source, encoding="utf-8")
    print(f"UPDATED: {path}")
PY

lake env lean HodgeProofHP/Stage3ComplexGaussianBound.lean
lake build HodgeProofHP.Stage3ComplexGaussianBound
