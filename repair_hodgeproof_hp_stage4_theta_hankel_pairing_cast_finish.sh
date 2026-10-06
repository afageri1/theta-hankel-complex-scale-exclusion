#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import shutil

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelAdjointSquarePairing.lean"),
    Path("create_hodgeproof_hp_stage4_theta_hankel_adjoint_square_pairing.sh"),
]

old = "  simp only [Complex.ofReal_pow]\n"
new = "  simp only [Complex.ofReal_pow] <;> rfl\n"

updates = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing {path}")
    raw = path.read_bytes()
    newline = "\r\n" if b"\r\n" in raw else "\n"
    text = raw.decode("utf-8").replace("\r\n", "\n")
    if new in text:
        print(f"ALREADY REPAIRED: {path}")
        continue
    if text.count(old) != 1:
        raise SystemExit(f"STOP: expected exactly one repair location in {path}")
    text = text.replace(old, new, 1)
    updates.append((path, text.replace("\n", newline).encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, data in updates:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    shutil.copy2(path, backup)
    path.write_bytes(data)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_theta_hankel_adjoint_square_pairing.sh
