#!/usr/bin/env bash
set -euo pipefail

python3 - <<'PY'
from pathlib import Path

paths = [
    Path("HodgeProofHP/Stage3GaussianSmooth.lean"),
    Path("create_hodgeproof_hp_stage3_gaussian_smooth.sh"),
]
old = "namespace HodgeProofHP\n\n"
new = "namespace HodgeProofHP\n\nopen scoped ContDiff\n\n"

updated = {}
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing {path}")
    source = path.read_text(encoding="utf-8")
    if source.count(old) != 1:
        raise SystemExit(f"STOP: expected one namespace header in {path}")
    updated[path] = source.replace(old, new, 1)

for path, source in updated.items():
    path.write_text(source, encoding="utf-8")
    print(f"UPDATED: {path}")
PY

lake env lean HodgeProofHP/Stage3GaussianSmooth.lean
lake build HodgeProofHP.Stage3GaussianSmooth
