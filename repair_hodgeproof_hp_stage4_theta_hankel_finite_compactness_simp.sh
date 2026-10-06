#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelFiniteCompactness.lean"),
    Path("create_hodgeproof_hp_stage4_theta_hankel_finite_compactness.sh"),
]

old = """      have hadd :
          ((hpThetaHankelBasisRankOne i +
              ∑ j ∈ F, hpThetaHankelBasisRankOne j) :
            HPThetaHankelSpace → HPThetaHankelSpace) =
          (hpThetaHankelBasisRankOne i :
            HPThetaHankelSpace → HPThetaHankelSpace) +
          ((∑ j ∈ F, hpThetaHankelBasisRankOne j) :
            HPThetaHankelSpace → HPThetaHankelSpace) := by
        funext x
        rfl
      rw [hadd]
      have hcompact :=
        (hpThetaHankelBasisRankOne_isCompact i).add ih
      simpa only [IsCompactOperator] using hcompact"""

new = """      simpa only [IsCompactOperator, ContinuousLinearMap.coe_add] using
        (hpThetaHankelBasisRankOne_isCompact i).add ih"""

prepared = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")
    raw = path.read_bytes()
    text = raw.decode("utf-8").replace("\r\n", "\n")
    count = text.count(old)
    if count != 1:
        raise SystemExit(
            f"STOP: expected one matching block in {path}; found {count}"
        )
    updated = text.replace(old, new, 1)
    if b"\r\n" in raw:
        updated = updated.replace("\n", "\r\n")
    prepared.append((path, raw, updated.encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, raw, updated in prepared:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(raw)
    path.write_bytes(updated)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_theta_hankel_finite_compactness.sh
