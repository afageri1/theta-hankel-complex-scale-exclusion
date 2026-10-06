#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import shutil

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelFiniteSpectralSecondDerivative.lean"),
    Path("create_hodgeproof_hp_stage4_theta_finite_spectral_second_derivative.sh"),
]

replacements = [
    (
"""  simpa only [hf0, hg0, hdf0, hdg0, mul_one, one_mul,
    zero_mul, mul_zero, add_zero, zero_add] using hsum.deriv""",
"""  have hd := hsum.deriv
  simp only [hf0, hg0, hdf0, hdg0, mul_one, one_mul,
    zero_mul, mul_zero, add_zero, zero_add] at hd
  convert hd using 1 <;> rfl"""
    ),
    (
"""  convert h using 1 <;>
    simp only [hpThetaHankelSpectralProductFactor,
      Nat.cast_ofNat, pow_one, id_eq] <;>
    ring""",
"""  convert h using 1 <;>
    norm_num [hpThetaHankelSpectralProductFactor, Pi.pow_apply] <;>
    ring"""
    ),
    (
"""  simpa only [mul_one] using
    ((hasDerivAt_id (0 : ℂ)).const_mul (-2 * i.1)).deriv""",
"""  have h := ((hasDerivAt_id (0 : ℂ)).const_mul (-2 * i.1)).deriv
  simp only [mul_one] at h
  convert h using 1 <;> rfl"""
    ),
]

prepared = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")
    raw = path.read_bytes()
    text = raw.decode("utf-8").replace("\r\n", "\n")
    for old, new in replacements:
        count = text.count(old)
        if count != 1:
            raise SystemExit(
                f"STOP: {path}: expected one matching block, found {count}\n{old}"
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

bash create_hodgeproof_hp_stage4_theta_finite_spectral_second_derivative.sh
