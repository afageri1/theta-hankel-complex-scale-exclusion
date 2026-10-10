#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelSpectralProductUniform.lean"),
    Path("create_hodgeproof_hp_stage4_theta_hankel_spectral_product_uniform.sh"),
]

old = """@[instance_reducible]
local instance hpThetaSpectralProductNormedCommRing : NormedCommRing ℂ :=
  { (inferInstance : NormedCommRing ℂ) with
    toCommRing := Complex.commRing }"""

new = """@[instance_reducible]
local instance hpThetaSpectralProductNormedCommRing : NormedCommRing ℂ :=
  @NormedField.toNormedCommRing ℂ Complex.instNormedField

-- Check that the product theorem uses the canonical complex monoid.
example :
    hpThetaSpectralProductNormedCommRing.toCommRing.toCommMonoid =
      Complex.commRing.toCommMonoid := by
  rfl"""

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
            f"STOP: {path}: expected 1 matching instance, found {count}"
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
