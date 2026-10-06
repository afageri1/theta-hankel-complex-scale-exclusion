#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelSpectralFamily.lean"),
    Path("create_hodgeproof_hp_stage4_theta_hankel_spectral_family.sh"),
]

old = """    hpThetaHankelAdjointSquare_eigenspaces_orthogonalFamily
      .orthonormal_sigma_orthonormal
        (fun ev => hpThetaHankelEigenspaceBasis_orthonormal ev)"""

new = """    OrthogonalFamily.orthonormal_sigma_orthonormal
      hpThetaHankelAdjointSquare_eigenspaces_orthogonalFamily
      (fun ev => hpThetaHankelEigenspaceBasis_orthonormal ev)"""

updates = []
for path in paths:
    data = path.read_bytes()
    text = data.decode("utf-8")
    newline = "\r\n" if "\r\n" in text else "\n"
    before = old.replace("\n", newline)
    after = new.replace("\n", newline)
    if text.count(before) != 1:
        raise SystemExit(f"STOP: {path}: expected exactly one matching block")
    updates.append((path, data, text.replace(before, after, 1).encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, original, repaired in updates:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(original)
    path.write_bytes(repaired)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_theta_hankel_spectral_family.sh
