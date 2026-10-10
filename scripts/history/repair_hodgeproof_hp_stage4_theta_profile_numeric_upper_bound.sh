#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import shutil

paths = [
    Path("HodgeProofHP/Stage4ThetaProfileNumericUpperBound.lean"),
    Path("create_hodgeproof_hp_stage4_theta_profile_numeric_upper_bound.sh"),
]

old = "    simp only [h10, h20]\n    change\n"
new = "    simp only [h10, h20]\n    simp only [mul_assoc]\n    change\n"

updates = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing {path}")
    raw = path.read_bytes()
    newline = b"\r\n" if b"\r\n" in raw else b"\n"
    text = raw.decode("utf-8").replace("\r\n", "\n")
    if new in text:
        print(f"ALREADY REPAIRED: {path}")
        continue
    if text.count(old) != 1:
        raise SystemExit(f"STOP: expected exactly one repair location in {path}")
    updated = text.replace(old, new, 1)
    updates.append((path, updated.replace("\n", newline.decode()).encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, data in updates:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    shutil.copy2(path, backup)
    path.write_bytes(data)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

lake env lean HodgeProofHP/Stage4ThetaProfileNumericUpperBound.lean
lake build HodgeProofHP.Stage4ThetaProfileNumericUpperBound

printf '%s\n' 'PASS: Stage4ThetaProfileNumericUpperBound'
