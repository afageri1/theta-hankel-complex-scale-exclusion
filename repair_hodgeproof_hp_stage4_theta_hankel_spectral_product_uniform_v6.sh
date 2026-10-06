#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelSpectralProductUniform.lean"),
    Path("create_hodgeproof_hp_stage4_theta_hankel_spectral_product_uniform.sh"),
]

old = """  simpa only [
    hpThetaHankelSpectralProduct,
    hpThetaHankelSpectralProductFactor,
    sub_eq_add_neg
  ] using h"""

new = """  change HasProdUniformlyOn
    (fun i : HPThetaHankelSpectralIndex =>
      fun z : ℂ => 1 + -(z ^ 2 * i.1))
    (fun z : ℂ =>
      ∏' i : HPThetaHankelSpectralIndex, (1 + -(z ^ 2 * i.1)))
    K at h
  unfold hpThetaHankelSpectralProduct
  simpa only [
    hpThetaHankelSpectralProductFactor,
    sub_eq_add_neg
  ] using h"""

changes = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing {path}")
    original = path.read_bytes()
    text = original.decode("utf-8")
    newline = "\r\n" if "\r\n" in text else "\n"
    needle = old.replace("\n", newline)
    replacement = new.replace("\n", newline)
    count = text.count(needle)
    if count != 1:
        raise SystemExit(
            f"STOP: {path}: expected 1 matching proof block, found {count}"
        )
    updated = text.replace(needle, replacement, 1).encode("utf-8")
    changes.append((path, original, updated))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, original, updated in changes:
    backup = Path(str(path) + ".before_repair_" + stamp)
    backup.write_bytes(original)
    path.write_bytes(updated)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_theta_hankel_spectral_product_uniform.sh
