#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaFirstTraceMoments.lean"),
    Path("create_hodgeproof_hp_stage4_theta_first_trace_moments.sh"),
]

old = """  simpa only [hpThetaPhiMomentZero, integral_ofReal]
    using h.symm"""

new = """  change
    ((∫ u in Set.Ioi 0,
      hpRiemannThetaDifferentialKernel u) : ℂ) =
        hpRiemannXiCritical 0
  calc
    ((∫ u in Set.Ioi 0,
        hpRiemannThetaDifferentialKernel u) : ℂ) =
        ∫ u in Set.Ioi 0,
          (hpRiemannThetaDifferentialKernel u : ℂ) :=
      (integral_complex_ofReal
        (f := hpRiemannThetaDifferentialKernel)
        (μ := volume.restrict (Set.Ioi 0))).symm
    _ = hpRiemannXiCritical 0 := h.symm"""

pending = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing {path}")
    raw = path.read_bytes()
    text = raw.decode("utf-8").replace("\r\n", "\n")
    count = text.count(old)
    if count != 1:
        raise SystemExit(
            f"STOP: expected exactly one matching block in {path}; found {count}"
        )
    updated = text.replace(old, new, 1)
    if b"\r\n" in raw:
        updated = updated.replace("\n", "\r\n")
    pending.append((path, raw, updated.encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")

for path, raw, updated in pending:
    backup = Path(str(path) + ".before_repair_" + stamp)
    backup.write_bytes(raw)
    print(f"BACKUP: {backup}")

for path, raw, updated in pending:
    path.write_bytes(updated)
    print(f"REPAIRED: {path}")
PY

lake env lean HodgeProofHP/Stage4ThetaFirstTraceMoments.lean
lake build HodgeProofHP.Stage4ThetaFirstTraceMoments

echo "PASS: Stage4ThetaFirstTraceMoments"
