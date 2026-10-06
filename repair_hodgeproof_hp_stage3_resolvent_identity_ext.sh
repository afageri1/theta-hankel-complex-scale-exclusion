#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage3UnitImaginaryResolventIdentity.lean"),
    Path("create_hodgeproof_hp_stage3_unit_imaginary_resolvent_identity.sh"),
]

old = "  ext v\n"
new = "  apply ContinuousLinearMap.ext\n  intro v\n"

prepared = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")
    original = path.read_text(encoding="utf-8")
    count = original.count(old)
    if count != 2:
        raise SystemExit(
            f"STOP: expected two matching blocks in {path}; found {count}"
        )
    prepared.append((path, original, original.replace(old, new)))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, original, updated in prepared:
    backup = path.with_name(path.name + ".before_ext_repair_" + stamp)
    backup.write_text(original, encoding="utf-8")
    path.write_text(updated, encoding="utf-8")
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

bash ./create_hodgeproof_hp_stage3_unit_imaginary_resolvent_identity.sh
