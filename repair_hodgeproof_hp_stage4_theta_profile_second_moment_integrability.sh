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
    Path("HodgeProofHP/Stage4ThetaProfileSecondMomentIntegrability.lean"),
    Path("create_hodgeproof_hp_stage4_theta_profile_second_moment_integrability.sh"),
]

old = """      rw [norm_mul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos (2 * u))]"""

new = """      simp only [norm_mul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos (2 * u))]"""

updates = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"ERROR: missing file: {path}")
    raw = path.read_bytes()
    text = raw.decode("utf-8").replace("\r\n", "\n")
    count = text.count(old)
    if count != 1:
        raise SystemExit(
            f"ERROR: expected one matching block in {path}; found {count}. "
            "No files changed."
        )
    updated = text.replace(old, new, 1)
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

lake env lean HodgeProofHP/Stage4ThetaProfileSecondMomentIntegrability.lean
lake build HodgeProofHP.Stage4ThetaProfileSecondMomentIntegrability

echo "PASS: Stage4ThetaProfileSecondMomentIntegrability"
