#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelSpectralProductEntire.lean"),
    Path("create_hodgeproof_hp_stage4_theta_spectral_product_entire.sh"),
]

old = "(isOpen_ball.mem_nhds hz)"
new = "(IsOpen.mem_nhds Metric.isOpen_ball hz)"

prepared = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing {path}")
    original = path.read_bytes()
    text = original.decode("utf-8")
    count = text.count(old)
    if count != 1:
        raise SystemExit(
            f"STOP: {path}: expected 1 occurrence, found {count}"
        )
    prepared.append((path, original, text.replace(old, new, 1).encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, original, updated in prepared:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(original)
    path.write_bytes(updated)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_theta_spectral_product_entire.sh
