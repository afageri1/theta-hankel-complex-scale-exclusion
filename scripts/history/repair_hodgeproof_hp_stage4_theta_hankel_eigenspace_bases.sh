#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelEigenspaceBases.lean"),
    Path("create_hodgeproof_hp_stage4_theta_hankel_eigenspace_bases.sh"),
]
old = b"abbrev hpThetaHankelEigenspace (ev : "
new = b"noncomputable abbrev hpThetaHankelEigenspace (ev : "

updates = []
for path in paths:
    data = path.read_bytes()
    if data.count(old) != 1 or new in data:
        raise SystemExit(f"STOP: {path}: expected one unrepaired declaration")
    updates.append((path, data, data.replace(old, new, 1)))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, original, repaired in updates:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(original)
    path.write_bytes(repaired)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_theta_hankel_eigenspace_bases.sh
