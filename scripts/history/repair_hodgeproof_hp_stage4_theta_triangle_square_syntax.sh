#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import re

paths = [
    Path("HodgeProofHP/Stage4ThetaTriangleSquareLIntegral.lean"),
    Path("create_hodgeproof_hp_stage4_theta_triangle_square_lintegral.sh"),
]

pattern = re.compile(
    r"\(measurePreserving_add_left \(volume : Measure ℝ\) x\)\."
    r"[ \t]*\r?\n[ \t]*setLIntegral_comp_preimage"
)
replacement = (
    "(measurePreserving_add_left (volume : Measure ℝ) x)"
    ".setLIntegral_comp_preimage"
)

updates = []
for p in paths:
    if not p.is_file():
        raise SystemExit(f"STOP: missing file: {p}")
    original = p.read_bytes()
    text = original.decode("utf-8")
    repaired, count = pattern.subn(replacement, text)
    if count != 1:
        raise SystemExit(
            f"STOP: {p}: expected one matching call, found {count}"
        )
    updates.append((p, original, repaired.encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for p, original, repaired in updates:
    backup = p.with_name(p.name + ".before_syntax_repair_" + stamp)
    backup.write_bytes(original)
    p.write_bytes(repaired)
    print("BACKUP:", backup)
    print("REPAIRED:", p)
PY

mkdir -p stage4_fourth_certificate_build_logs
log=stage4_fourth_certificate_build_logs/triangle_square_syntax_repair.log

if lake build HodgeProofHP.Stage4ThetaTriangleSquareLIntegral >"$log" 2>&1; then
    tail -n 40 "$log"
    echo "PASS: Stage4ThetaTriangleSquareLIntegral"
else
    tail -n 100 "$log"
    echo "STOP: build failed; log: $log"
    exit 1
fi
