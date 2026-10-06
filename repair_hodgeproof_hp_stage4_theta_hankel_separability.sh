#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelSeparability.lean"),
    Path("create_hodgeproof_hp_stage4_theta_hankel_separability.sh"),
]

replacements = [
    ("(2 : ℝ≥0∞)", "(2 : ENNReal)", 2),
    ("SeparableSpace HPThetaHankelSpace",
     "TopologicalSpace.SeparableSpace HPThetaHankelSpace", 2),
]

prepared = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing {path}")
    raw = path.read_bytes()
    text = raw.decode("utf-8").replace("\r\n", "\n")
    for old, new, expected in replacements:
        count = text.count(old)
        if count != expected:
            raise SystemExit(
                f"STOP: {path}: expected {expected} occurrences "
                f"of {old!r}; found {count}"
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
