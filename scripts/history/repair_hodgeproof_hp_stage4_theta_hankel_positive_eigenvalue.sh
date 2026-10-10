#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelPositiveEigenvalue.lean"),
    Path("create_hodgeproof_hp_stage4_theta_hankel_positive_eigenvalue.sh"),
]

replacements = [
    (
        "    ext f\n"
        "    apply (hpThetaHankelAdjointSquare_apply_eq_zero_iff f).mp",
        "    apply ContinuousLinearMap.ext\n"
        "    intro f\n"
        "    change hpThetaHankelOperator f = 0\n"
        "    apply (hpThetaHankelAdjointSquare_apply_eq_zero_iff f).mp",
    ),
    (
        "(hpThetaHankelAdjointSquare_isCompact\n"
        "      .hasEigenvalue_iff_mem_spectrum hev).mp hEig",
        "(hpThetaHankelAdjointSquare_isCompact.hasEigenvalue_iff_mem_spectrum\n"
        "      hev).mp hEig",
    ),
]

prepared = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")
    original = path.read_bytes()
    updated = original
    newline = b"\r\n" if b"\r\n" in original else b"\n"
    for old, new in replacements:
        old_bytes = old.encode("utf-8").replace(b"\n", newline)
        new_bytes = new.encode("utf-8").replace(b"\n", newline)
        count = updated.count(old_bytes)
        if count != 1:
            raise SystemExit(
                f"STOP: {path}: expected 1 occurrence, found {count}"
            )
        updated = updated.replace(old_bytes, new_bytes, 1)
    prepared.append((path, original, updated))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, original, updated in prepared:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(original)
    path.write_bytes(updated)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_theta_hankel_positive_eigenvalue.sh
