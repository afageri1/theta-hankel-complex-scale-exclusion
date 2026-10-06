#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelTailEnergyBounds.lean"),
    Path("create_hodgeproof_hp_stage4_theta_hankel_tail_energy_bounds.sh"),
]

old = "open scoped BigOperators\n"
new = """open scoped BigOperators

local instance : DecidableEq hpThetaHankelBasisSet :=
  Classical.decEq _
"""

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
updates = []

for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")
    raw = path.read_bytes()
    text = raw.decode("utf-8").replace("\r\n", "\n")
    if text.count(old) != 1:
        raise SystemExit(f"STOP: expected exactly one matching anchor: {path}")
    if "local instance : DecidableEq hpThetaHankelBasisSet" in text:
        raise SystemExit(f"STOP: repair already present: {path}")
    repaired = text.replace(old, new, 1)
    if b"\r\n" in raw:
        repaired = repaired.replace("\n", "\r\n")
    updates.append((path, raw, repaired.encode("utf-8")))

for path, raw, repaired in updates:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(raw)
    path.write_bytes(repaired)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_theta_hankel_tail_energy_bounds.sh
