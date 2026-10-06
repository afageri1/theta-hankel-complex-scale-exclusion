#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import shutil

paths = [
    Path("HodgeProofHP/Stage4ThetaProfileGeometricUpperBound.lean"),
    Path("create_hodgeproof_hp_stage4_theta_profile_geometric_upper_bound.sh"),
]

old = b"      tsum_le_tsum hpoint hactual hgeom.summable"
new = b"      Summable.tsum_le_tsum hpoint hactual hgeom.summable"

prepared = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")
    data = path.read_bytes()
    if data.count(old) == 1:
        prepared.append((path, data.replace(old, new)))
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

lake env lean HodgeProofHP/Stage4ThetaProfileGeometricUpperBound.lean
lake build HodgeProofHP.Stage4ThetaProfileGeometricUpperBound

printf '%s\n' 'PASS: Stage4ThetaProfileGeometricUpperBound'
