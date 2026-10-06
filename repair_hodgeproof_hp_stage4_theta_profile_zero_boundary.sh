#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaProfileZeroBoundary.lean"),
    Path("create_hodgeproof_hp_stage4_theta_profile_zero_boundary.sh"),
]

old = "    rw [Real.exp_rpow]\n"
new = (
    "    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]\n"
)

prepared = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")
    raw = path.read_bytes()
    text = raw.decode("utf-8").replace("\r\n", "\n")
    count = text.count(old)
    if count != 1:
        raise SystemExit(
            f"STOP: expected exactly one target in {path}; found {count}"
        )
    fixed = text.replace(old, new)
    if b"\r\n" in raw:
        fixed = fixed.replace("\n", "\r\n")
    prepared.append((path, raw, fixed.encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, raw, _ in prepared:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(raw)
    print(f"BACKUP: {backup}")

for path, _, fixed in prepared:
    path.write_bytes(fixed)
    print(f"REPAIRED: {path}")
PY

lake env lean HodgeProofHP/Stage4ThetaProfileZeroBoundary.lean
lake build HodgeProofHP.Stage4ThetaProfileZeroBoundary
