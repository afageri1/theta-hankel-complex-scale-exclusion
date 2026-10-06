#!/usr/bin/env bash
set -euo pipefail

command -v lake >/dev/null || {
  echo "ERROR: lake not found"
  exit 1
}

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaFiniteSecondMomentIBP.lean"),
    Path("create_hodgeproof_hp_stage4_theta_finite_second_moment_ibp.sh"),
]

old = """  convert hleft.sub hright using 1
  · funext x
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
    ring
  · simp only [Pi.mul_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat]
    norm_num
    ring"""

new = """  convert hleft.sub hright using 1
  · funext x
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, id_eq] <;> ring
  · simp only [Pi.mul_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat] <;>
      norm_num <;> ring"""

updates = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"ERROR: missing file: {path}")
    raw = path.read_bytes()
    text = raw.decode("utf-8")
    normalized = text.replace("\r\n", "\n")
    count = normalized.count(old)
    if count != 1:
        raise SystemExit(
            f"ERROR: expected one matching proof in {path}; found {count}. "
            "No files changed."
        )
    updated = normalized.replace(old, new, 1)
    if b"\r\n" in raw:
        updated = updated.replace("\n", "\r\n")
    updates.append((path, raw, updated.encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, raw, updated in updates:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(raw)
    path.write_bytes(updated)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

lake env lean HodgeProofHP/Stage4ThetaFiniteSecondMomentIBP.lean
lake build HodgeProofHP.Stage4ThetaFiniteSecondMomentIBP

echo "PASS: Stage4ThetaFiniteSecondMomentIBP"
