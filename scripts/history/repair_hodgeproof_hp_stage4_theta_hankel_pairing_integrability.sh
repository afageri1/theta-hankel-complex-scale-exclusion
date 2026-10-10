#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelPairingIntegrability.lean"),
    Path("create_hodgeproof_hp_stage4_theta_hankel_pairing_integrability.sh"),
]

old = """        ((fun p : ℝ × ℝ => star (f p.1)) *
          (fun p : ℝ × ℝ => g p.2)) ="""

new = """        ((star (fun p : ℝ × ℝ => f p.1)) *
          (fun p : ℝ × ℝ => g p.2)) ="""

prepared = []
for path in paths:
    raw = path.read_bytes()
    text = raw.decode("utf-8").replace("\r\n", "\n")
    count = text.count(old)
    if count != 1:
        raise SystemExit(
            f"STOP: {path}: expected one match, found {count}"
        )
    prepared.append((path, raw, text.replace(old, new, 1)))

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

lake env lean HodgeProofHP/Stage4ThetaHankelPairingIntegrability.lean
lake build HodgeProofHP.Stage4ThetaHankelPairingIntegrability
echo "PASS: Stage4ThetaHankelPairingIntegrability"
