#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import shutil

paths = [
    Path("HodgeProofHP/Stage3CompactResolventSpectrum.lean"),
    Path("create_hodgeproof_hp_stage3_compact_resolvent_spectrum.sh"),
]

old = "T.toLinearMap.HasEigenvalue μ"
new = "Module.End.HasEigenvalue T.toLinearMap μ"

updates = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")
    data = path.read_bytes()
    text = data.decode("utf-8")
    count = text.count(old)
    if count != 1:
        raise SystemExit(
            f"STOP: expected exactly one occurrence in {path}; found {count}"
        )
    updates.append((path, text.replace(old, new).encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")

for path, _ in updates:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    shutil.copy2(path, backup)
    print(f"BACKUP: {backup}")

for path, data in updates:
    path.write_bytes(data)
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage3_compact_resolvent_spectrum.sh
