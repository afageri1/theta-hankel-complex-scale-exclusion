#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import shutil

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelFiniteSpectralFourthDerivative.lean"),
    Path("create_hodgeproof_hp_stage4_theta_hankel_finite_spectral_fourth_derivative.sh"),
]

old = """  | empty =>
      simp [hpThetaHankelFiniteSpectralProduct,
        hpThetaIteratedComplexDeriv]
"""

new = """  | empty =>
      have hfun :
          hpThetaHankelFiniteSpectralProduct ∅ =
            (fun _ : ℂ => 1) := by
        funext z
        simp [hpThetaHankelFiniteSpectralProduct]
      rw [hfun]
      simp [hpThetaIteratedComplexDeriv]
"""

updates = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")
    raw = path.read_bytes()
    newline = b"\r\n" if b"\r\n" in raw else b"\n"
    source = raw.decode("utf-8").replace("\r\n", "\n")
    count = source.count(old)
    if count != 1:
        raise SystemExit(
            f"STOP: {path}: expected 1 matching block, found {count}"
        )
    revised = source.replace(old, new, 1)
    updates.append((path, revised.replace("\n", newline.decode()).encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, revised in updates:
    backup = Path(str(path) + ".before_repair_" + stamp)
    shutil.copy2(path, backup)
    print(f"BACKUP: {backup}")
    path.write_bytes(revised)
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_theta_hankel_finite_spectral_fourth_derivative.sh
