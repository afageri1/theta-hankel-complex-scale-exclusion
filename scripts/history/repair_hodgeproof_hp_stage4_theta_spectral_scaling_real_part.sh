#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import shutil

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelSpectralScalingNecessary.lean"),
    Path("create_hodgeproof_hp_stage4_theta_spectral_scaling_necessary.sh"),
]

old = """  rw [hpThetaHankelScaledSpectralProduct_secondDeriv_zero]
  rw [← Complex.ofReal_pow]
  simp"""

new = """  rw [hpThetaHankelScaledSpectralProduct_secondDeriv_zero]
  norm_num [pow_two, Complex.mul_re, Complex.mul_im] <;> ring"""

prepared = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")
    raw = path.read_bytes()
    text = raw.decode("utf-8").replace("\r\n", "\n")
    count = text.count(old)
    if count != 1:
        raise SystemExit(
            f"STOP: {path}: expected one matching block, found {count}"
        )
    text = text.replace(old, new, 1)
    newline = "\r\n" if b"\r\n" in raw else "\n"
    prepared.append((path, text.replace("\n", newline).encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, content in prepared:
    backup = Path(str(path) + ".before_repair_" + stamp)
    shutil.copy2(path, backup)
    print(f"BACKUP: {backup}")
    path.write_bytes(content)
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_theta_spectral_scaling_necessary.sh
