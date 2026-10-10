#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelSingleSpectralBound.lean"),
    Path("create_hodgeproof_hp_stage4_theta_hankel_single_spectral_bound.sh"),
]

old = "  field_simp [hne]"
new = "  exact div_mul_cancel₀ (i.1.re ^ 2) hne"

updates = []
for path in paths:
    raw = path.read_bytes()
    newline = "\r\n" if b"\r\n" in raw else "\n"
    text = raw.decode("utf-8").replace("\r\n", "\n")
    count = text.count(old)
    if count != 1:
        raise SystemExit(
            f"STOP: {path}: expected 1 matching block, found {count}"
        )
    updated = text.replace(old, new).replace("\n", newline).encode("utf-8")
    updates.append((path, raw, updated))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, raw, updated in updates:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(raw)
    path.write_bytes(updated)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_theta_hankel_single_spectral_bound.sh
