#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelSeparability.lean"),
    Path("create_hodgeproof_hp_stage4_theta_hankel_separability.sh"),
]

old = "Fact ((2 : ENNReal) ≠ ∞)"
new = "Fact ((2 : ENNReal) ≠ (⊤ : ENNReal))"

prepared = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing {path}")
    raw = path.read_bytes()
    text = raw.decode("utf-8").replace("\r\n", "\n")
    count = text.count(old)
    if count != 1:
        raise SystemExit(
            f"STOP: expected one matching expression in {path}; found {count}"
        )
    text = text.replace(old, new)
    if b"\r\n" in raw:
        text = text.replace("\n", "\r\n")
    prepared.append((path, raw, text.encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, raw, updated in prepared:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(raw)
    path.write_bytes(updated)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_theta_hankel_separability.sh
