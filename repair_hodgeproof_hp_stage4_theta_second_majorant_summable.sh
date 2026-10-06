#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaSecondMajorantSummable.lean"),
    Path("create_hodgeproof_hp_stage4_theta_second_majorant_summable.sh"),
]

old = "Real.exp_zero, mul_one, hquarter] using"
new = "Real.exp_zero, mul_one, hquarter, neg_mul] using"

updates = []
for path in paths:
    raw = path.read_bytes()
    text = raw.decode("utf-8")
    if text.count(old) != 1:
        raise SystemExit(f"STOP: expected one matching line in {path}")
    updates.append((path, raw, text.replace(old, new).encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, raw, updated in updates:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(raw)
    print(f"BACKUP: {backup}")

for path, raw, updated in updates:
    path.write_bytes(updated)
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_theta_second_majorant_summable.sh
