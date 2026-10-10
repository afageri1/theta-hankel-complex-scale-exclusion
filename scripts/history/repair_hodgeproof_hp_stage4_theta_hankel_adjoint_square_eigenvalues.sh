#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import shutil

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelAdjointSquareEigenvalues.lean"),
    Path("create_hodgeproof_hp_stage4_theta_hankel_adjoint_square_eigenvalues.sh"),
]

updates = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")
    data = path.read_bytes()
    text = data.decode("utf-8")
    count = text.count("λ")
    if count != 17:
        raise SystemExit(
            f"STOP: {path}: expected 17 occurrences of λ, found {count}"
        )
    updates.append((path, text.replace("λ", "ev").encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, data in updates:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    shutil.copy2(path, backup)
    path.write_bytes(data)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_theta_hankel_adjoint_square_eigenvalues.sh
