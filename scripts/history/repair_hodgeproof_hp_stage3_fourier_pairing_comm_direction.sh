#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import shutil

paths = [
    Path("HodgeProofHP/Stage3GaussianFourierPairing.lean"),
    Path("create_hodgeproof_hp_stage3_gaussian_fourier_pairing.sh"),
]

old = "    exact real_inner_comm y x"
new = "    exact (real_inner_comm y x).symm"
stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
updates = []

for path in paths:
    text = path.read_text(encoding="utf-8")
    if old in text:
        updates.append((path, text.replace(old, new)))
    elif new in text:
        print(f"Already repaired: {path}")
    else:
        raise SystemExit(f"STOP: expected proof not found in {path}")

for path, text in updates:
    shutil.copy2(path, str(path) + ".bak." + stamp)
    path.write_text(text, encoding="utf-8")
    print(f"Repaired: {path}")
PY

bash create_hodgeproof_hp_stage3_gaussian_fourier_pairing.sh
