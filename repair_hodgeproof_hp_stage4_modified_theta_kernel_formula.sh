#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ModifiedThetaKernelFormula.lean"),
    Path("create_hodgeproof_hp_stage4_modified_theta_kernel_formula.sh"),
]

old = "Set.indicator_of_not_mem"
new = "Set.indicator_of_notMem"
stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
updates = []

# Validate both files before changing either.
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")

    raw = path.read_bytes()
    text = raw.decode("utf-8")
    count = text.count(old)

    if count != 4:
        raise SystemExit(
            f"STOP: {path}: expected 4 occurrences, found {count}"
        )

    updates.append((path, raw, text.replace(old, new).encode("utf-8")))

# Back up all files before writing changes.
for path, raw, _ in updates:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(raw)
    print(f"BACKUP: {backup}")

for path, _, revised in updates:
    path.write_bytes(revised)
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_modified_theta_kernel_formula.sh
