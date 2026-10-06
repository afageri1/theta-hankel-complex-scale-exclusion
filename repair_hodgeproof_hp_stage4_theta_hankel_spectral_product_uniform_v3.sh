#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelSpectralProductUniform.lean"),
    Path("create_hodgeproof_hp_stage4_theta_hankel_spectral_product_uniform.sh"),
]

edits = [
    (
        """    toCommRing := Complex.commRing }""",
        """    toCommRing := Complex.commRing }

attribute [local reducible] hpThetaSpectralProductNormedCommRing"""
    ),
    (
        """      hK hu hmajor hcts
  simpa only [""",
        """      hK hu hmajor hcts
  dsimp only [hpThetaSpectralProductNormedCommRing] at h
  simpa only ["""
    ),
    (
        """end HodgeProofHP""",
        """end

end HodgeProofHP"""
    ),
]

changes = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing {path}")
    original = path.read_bytes()
    text = original.decode("utf-8")
    newline = "\r\n" if "\r\n" in text else "\n"
    if "attribute [local reducible] hpThetaSpectralProductNormedCommRing" in text:
        raise SystemExit(f"STOP: repair already present in {path}")
    for old, new in edits:
        needle = old.replace("\n", newline)
        replacement = new.replace("\n", newline)
        count = text.count(needle)
        if count != 1:
            raise SystemExit(
                f"STOP: {path}: expected 1 match, found {count}: {old!r}"
            )
        text = text.replace(needle, replacement, 1)
    changes.append((path, original, text.encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, original, updated in changes:
    backup = Path(str(path) + ".before_repair_" + stamp)
    backup.write_bytes(original)
    path.write_bytes(updated)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_theta_hankel_spectral_product_uniform.sh
