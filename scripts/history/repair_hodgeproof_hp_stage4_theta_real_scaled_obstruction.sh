#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import shutil

paths = [
    Path("HodgeProofHP/Stage4ThetaRealScaledObstruction.lean"),
    Path("create_hodgeproof_hp_stage4_theta_real_scaled_obstruction.sh"),
]
old = "  simp only [hpThetaXiMomentRatio] at h\n"

prepared = []
for p in paths:
    if not p.is_file():
        raise SystemExit(f"STOP: missing {p}")
    raw = p.read_bytes()
    text = raw.decode("utf-8").replace("\r\n", "\n")
    count = text.count(old)
    if count != 1:
        raise SystemExit(
            f"STOP: {p}: expected one matching line, found {count}"
        )
    fixed = text.replace(old, "", 1)
    newline = "\r\n" if b"\r\n" in raw else "\n"
    prepared.append((p, fixed.replace("\n", newline).encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for p, data in prepared:
    backup = p.with_name(p.name + ".before_simp_repair_" + stamp)
    shutil.copy2(p, backup)
    p.write_bytes(data)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {p}")
PY

mkdir -p stage4_fourth_certificate_build_logs
log="stage4_fourth_certificate_build_logs/real_scaled_obstruction_repair.log"

if lake build HodgeProofHP.Stage4ThetaRealScaledObstruction >"$log" 2>&1; then
    tail -n 65 "$log"
    echo "PASS: Stage4ThetaRealScaledObstruction"
else
    tail -n 110 "$log"
    echo "STOP: build failed; log: $log"
    exit 1
fi
