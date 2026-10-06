#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaFiniteSecondMomentIBP.lean"),
    Path("create_hodgeproof_hp_stage4_theta_finite_second_moment_ibp.sh"),
]

old = """  convert hleft.sub hright using 1 <;> ring"""

new = """  convert hleft.sub hright using 1
  · funext x
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
    ring
  · simp only [Pi.mul_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat]
    norm_num
    ring"""

updates = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")
    raw = path.read_bytes()
    text = raw.decode("utf-8-sig").replace("\r\n", "\n")
    if text.count(old) != 1:
        raise SystemExit(
            f"STOP: expected exactly one repair location in {path}; "
            f"found {text.count(old)}"
        )
    repaired = text.replace(old, new, 1)
    if b"\r\n" in raw:
        repaired = repaired.replace("\n", "\r\n")
    updates.append((path, raw, repaired.encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, original, repaired in updates:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(original)
    path.write_bytes(repaired)
    print("BACKUP:", backup)
    print("REPAIRED:", path)
PY

lake env lean HodgeProofHP/Stage4ThetaFiniteSecondMomentIBP.lean
lake build HodgeProofHP.Stage4ThetaFiniteSecondMomentIBP

echo "PASS: Stage4ThetaFiniteSecondMomentIBP"
