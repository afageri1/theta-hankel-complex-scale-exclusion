#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import shutil

paths = [
    Path("HodgeProofHP/Stage4ThetaTangentTailBound.lean"),
    Path("create_hodgeproof_hp_stage4_theta_tangent_tail_bound.sh"),
]

old = b"rw [intervalIntegral.integral_div_const]"
new = b"rw [intervalIntegral.integral_div]"

prepared = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")
    data = path.read_bytes()
    if data.count(old) == 1:
        prepared.append((path, data.replace(old, new, 1)))
    elif data.count(old) == 0 and data.count(new) == 1:
        print(f"ALREADY REPAIRED: {path}")
    else:
        raise SystemExit(f"STOP: unexpected matching text in {path}")

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, updated in prepared:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    shutil.copy2(path, backup)
    path.write_bytes(updated)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

lake env lean HodgeProofHP/Stage4ThetaTangentTailBound.lean
lake build HodgeProofHP.Stage4ThetaTangentTailBound

printf '%s\n' 'PASS: Stage4ThetaTangentTailBound'
