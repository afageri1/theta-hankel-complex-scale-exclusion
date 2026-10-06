#!/usr/bin/env bash
set -euo pipefail

if [[ ! -f lakefile.lean && ! -f lakefile.toml ]]; then
  echo "STOP: run from the hodgeproof-hp project root."
  exit 1
fi

python - <<'PY'
from pathlib import Path
from datetime import datetime
import shutil

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelSquareFiniteness.lean"),
    Path("create_hodgeproof_hp_stage4_theta_hankel_square_finiteness.sh"),
]

old = """  simpa only [← ofReal_norm_eq_enorm, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]
    using hpThetaHankelKernel_sq_lintegral_lt_top
"""

new = """  have hnorm (p : ℝ × ℝ) :
      ‖‖hpThetaHankelKernel p.1 p.2‖ ^ 2‖ₑ =
        ENNReal.ofReal (‖hpThetaHankelKernel p.1 p.2‖ ^ 2) := by
    rw [← ofReal_norm, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (‖hpThetaHankelKernel p.1 p.2‖))]
  simp_rw [hnorm]
  exact hpThetaHankelKernel_sq_lintegral_lt_top
"""

changes = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")
    raw = path.read_bytes()
    text = raw.decode("utf-8").replace("\r\n", "\n")
    if text.count(old) != 1:
        raise SystemExit(f"STOP: expected one proof-block match in {path}")
    if text.count("ofReal_norm_eq_enorm") != 2:
        raise SystemExit(f"STOP: unexpected lemma-name count in {path}")
    updated = text.replace(old, new, 1)
    updated = updated.replace("ofReal_norm_eq_enorm", "ofReal_norm")
    if b"\r\n" in raw:
        updated = updated.replace("\n", "\r\n")
    changes.append((path, updated.encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, _ in changes:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    shutil.copy2(path, backup)
    print(f"BACKUP: {backup}")

for path, content in changes:
    path.write_bytes(content)
    print(f"REPAIRED: {path}")
PY

lake env lean HodgeProofHP/Stage4ThetaHankelSquareFiniteness.lean
lake build HodgeProofHP.Stage4ThetaHankelSquareFiniteness

echo "PASS: Stage4ThetaHankelSquareFiniteness"
