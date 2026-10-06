#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelSpectralProductUniform.lean"),
    Path("create_hodgeproof_hp_stage4_theta_hankel_spectral_product_uniform.sh"),
]

old = "namespace HodgeProofHP\n"
new = """namespace HodgeProofHP

-- Keep the algebraic structure used by tprod and the normed-ring
-- product theorem on the same instance path.
local instance hpThetaSpectralProductNormedCommRing : NormedCommRing ℂ :=
  { (inferInstance : NormedRing ℂ), Complex.commRing with }
"""

changes = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing {path}")
    original = path.read_bytes()
    text = original.decode("utf-8")
    newline = "\r\n" if "\r\n" in text else "\n"
    needle = old.replace("\n", newline)
    replacement = new.replace("\n", newline)
    if "hpThetaSpectralProductNormedCommRing" in text:
        raise SystemExit(f"STOP: repair already present in {path}")
    count = text.count(needle)
    if count != 1:
        raise SystemExit(
            f"STOP: {path}: expected 1 namespace occurrence, found {count}"
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
