#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import shutil

paths = [
    Path("HodgeProofHP/Stage4ThetaTangentIntervalIntegral.lean"),
    Path("create_hodgeproof_hp_stage4_theta_tangent_interval_integral.sh"),
]

replacements = [
    (
        "simpa only [one_mul] using",
        "simpa only [id_eq, mul_one] using",
    ),
    (
        "dsimp <;> field_simp [hk] <;> ring",
        "field_simp [hk] <;> ring",
    ),
]

prepared = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")
    original = path.read_bytes()
    text = original.decode("utf-8")
    for old, new in replacements:
        if text.count(old) == 1:
            text = text.replace(old, new, 1)
        elif text.count(old) == 0 and text.count(new) == 1:
            pass
        else:
            raise SystemExit(f"STOP: unexpected matching text in {path}: {old}")
    updated = text.encode("utf-8")
    if updated != original:
        prepared.append((path, updated))
    else:
        print(f"ALREADY REPAIRED: {path}")

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, updated in prepared:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    shutil.copy2(path, backup)
    path.write_bytes(updated)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

lake env lean HodgeProofHP/Stage4ThetaTangentIntervalIntegral.lean
lake build HodgeProofHP.Stage4ThetaTangentIntervalIntegral

printf '%s\n' 'PASS: Stage4ThetaTangentIntervalIntegral'
