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
    Path("HodgeProofHP/Stage4ThetaHankelKernelL2.lean"),
    Path("create_hodgeproof_hp_stage4_theta_hankel_kernel_l2.sh"),
]

old = """def hpThetaHankelMeasure : Measure ℝ :=
  volume.restrict (Set.Ioi (0 : ℝ))

abbrev HPThetaHankelSpace :=
"""

new = """def hpThetaHankelMeasure : Measure ℝ :=
  volume.restrict (Set.Ioi (0 : ℝ))

instance hpThetaHankelMeasure_sFinite : SFinite hpThetaHankelMeasure := by
  unfold hpThetaHankelMeasure
  infer_instance

abbrev HPThetaHankelSpace :=
"""

changes = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")
    raw = path.read_bytes()
    text = raw.decode("utf-8").replace("\r\n", "\n")
    count = text.count(old)
    if count != 1:
        raise SystemExit(
            f"STOP: expected one match in {path}, found {count}"
        )
    updated = text.replace(old, new, 1)
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

lake env lean HodgeProofHP/Stage4ThetaHankelKernelL2.lean
lake build HodgeProofHP.Stage4ThetaHankelKernelL2

echo "PASS: Stage4ThetaHankelKernelL2"
