#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaTriangleTestVector.lean"),
    Path("create_hodgeproof_hp_stage4_theta_triangle_test_vector.sh"),
]

old = """  · simp only [hpThetaTriangleTestFunction,
      Set.indicator_of_notMem hx, norm_zero, zero_pow]"""

new = """  · simp only [hpThetaTriangleTestFunction,
      Set.indicator_of_notMem hx, norm_zero]
    norm_num"""

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
updates = []

for p in paths:
    if not p.is_file():
        raise SystemExit(f"STOP: missing {p}")
    raw = p.read_bytes()
    text = raw.decode("utf-8").replace("\r\n", "\n")
    count = text.count(old)
    if count != 1:
        raise SystemExit(
            f"STOP: {p}: expected one matching block, found {count}"
        )
    updated = text.replace(old, new)
    if b"\r\n" in raw:
        updated = updated.replace("\n", "\r\n")
    updates.append((p, raw, updated.encode("utf-8")))

for p, raw, updated in updates:
    backup = p.with_name(p.name + ".before_zero_repair_" + stamp)
    backup.write_bytes(raw)
    p.write_bytes(updated)
    print("BACKUP:", backup)
    print("REPAIRED:", p)
PY

mkdir -p stage4_fourth_certificate_build_logs
log=stage4_fourth_certificate_build_logs/triangle_test_vector_zero_repair.log

if lake build HodgeProofHP.Stage4ThetaTriangleTestVector >"$log" 2>&1; then
    tail -n 40 "$log"
    echo "PASS: Stage4ThetaTriangleTestVector"
else
    tail -n 100 "$log"
    echo "STOP: build failed; log: $log"
    exit 1
fi
