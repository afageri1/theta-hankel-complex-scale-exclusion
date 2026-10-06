#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelSpectralSummability.lean"),
    Path("create_hodgeproof_hp_stage4_theta_hankel_spectral_summability.sh"),
]

old = b"  simp [hpThetaHankelSpectralBasis_norm, hinner]"
new = b"  norm_num [hpThetaHankelSpectralBasis_norm, hinner]"

pending = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing {path}")
    data = path.read_bytes()
    data.decode("utf-8")
    count = data.count(old)
    if count != 1:
        raise SystemExit(
            f"STOP: {path}: expected 1 matching line, found {count}"
        )
    pending.append((path, data))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, data in pending:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(data)
    path.write_bytes(data.replace(old, new, 1))
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_theta_hankel_spectral_summability.sh
