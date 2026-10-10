#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelRowEnergy.lean"),
    Path("create_hodgeproof_hp_stage4_theta_hankel_row_energy.sh"),
]

old = "        simp only [Complex.ofReal_pow]"
new = "        simp only [Complex.ofReal_pow] <;> rfl"

prepared = []
for path in paths:
    raw = path.read_bytes()
    text = raw.decode("utf-8").replace("\r\n", "\n")
    count = text.count(old)
    if count != 2:
        raise SystemExit(
            f"STOP: {path}: expected 2 matches, found {count}"
        )
    prepared.append((path, raw, text.replace(old, new)))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, raw, text in prepared:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(raw)
    print("BACKUP:", backup)

for path, raw, text in prepared:
    if b"\r\n" in raw:
        text = text.replace("\n", "\r\n")
    path.write_bytes(text.encode("utf-8"))
    print("REPAIRED:", path)
PY

lake env lean HodgeProofHP/Stage4ThetaHankelRowEnergy.lean
lake build HodgeProofHP.Stage4ThetaHankelRowEnergy
echo "PASS: Stage4ThetaHankelRowEnergy"
