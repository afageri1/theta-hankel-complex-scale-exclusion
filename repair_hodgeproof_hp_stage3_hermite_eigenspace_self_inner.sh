#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage3HermiteEigenspaceSimple.lean"),
    Path("create_hodgeproof_hp_stage3_hermite_eigenspace_simple.sh"),
]

old = "    simp [hpHermiteCoefficient, inner_smul_right, hself]"
new = """    simp only [hpHermiteCoefficient, inner_smul_right,
      hself, mul_one]"""

prepared = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")
    original = path.read_text(encoding="utf-8")
    count = original.count(old)
    if count != 1:
        raise SystemExit(
            f"STOP: expected one matching block in {path}; found {count}"
        )
    prepared.append((path, original, original.replace(old, new, 1)))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, original, updated in prepared:
    backup = path.with_name(path.name + ".before_self_inner_" + stamp)
    backup.write_text(original, encoding="utf-8")
    path.write_text(updated, encoding="utf-8")
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

bash ./create_hodgeproof_hp_stage3_hermite_eigenspace_simple.sh
