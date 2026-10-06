#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelChosenDiagonalAbsolute.lean"),
    Path("create_hodgeproof_hp_stage4_theta_hankel_chosen_diagonal_absolute.sh"),
]

old_cast = """      (‖hpThetaHankelOperator
        (hpThetaHankelHilbertBasis i)‖ ^ 2 : ℂ) := by"""

new_cast = """      ((‖hpThetaHankelOperator
        (hpThetaHankelHilbertBasis i)‖ ^ 2 : ℝ) : ℂ) := by"""

old_norm = """  simp [Complex.norm_ofReal, abs_of_nonneg (sq_nonneg
    ‖hpThetaHankelOperator (hpThetaHankelHilbertBasis i)‖)]"""

new_norm = """  exact Complex.norm_of_nonneg
    (sq_nonneg ‖hpThetaHankelOperator (hpThetaHankelHilbertBasis i)‖)"""

pending = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing {path}")
    raw = path.read_bytes()
    text = raw.decode("utf-8").replace("\r\n", "\n")
    for old in (old_cast, old_norm):
        count = text.count(old)
        if count != 1:
            raise SystemExit(
                f"STOP: expected one matching block in {path}; found {count}"
            )
    updated = text.replace(old_cast, new_cast).replace(old_norm, new_norm)
    if b"\r\n" in raw:
        updated = updated.replace("\n", "\r\n")
    pending.append((path, raw, updated.encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, raw, updated in pending:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(raw)
    path.write_bytes(updated)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_theta_hankel_chosen_diagonal_absolute.sh
