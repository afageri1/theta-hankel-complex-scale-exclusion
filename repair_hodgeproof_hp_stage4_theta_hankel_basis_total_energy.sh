#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import shutil

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelBasisTotalEnergy.lean"),
    Path("create_hodgeproof_hp_stage4_theta_hankel_basis_total_energy.sh"),
]

old = """    (continuous_id.mul
      (hpRiemannThetaDifferentialKernel_continuous.pow 2))
        .measurable.aestronglyMeasurable"""

new = """    by
      have hc :
          Continuous
            (fun u : ℝ =>
              u * hpRiemannThetaDifferentialKernel u ^ 2) :=
        continuous_id.mul
          (hpRiemannThetaDifferentialKernel_continuous.pow 2)
      exact hc.measurable.aestronglyMeasurable"""

updates = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing {path}")
    raw = path.read_bytes()
    text = raw.decode("utf-8").replace("\r\n", "\n")
    if text.count(old) != 1:
        raise SystemExit(f"STOP: expected exactly one matching block in {path}")
    revised = text.replace(old, new, 1)
    if b"\r\n" in raw:
        revised = revised.replace("\n", "\r\n")
    updates.append((path, revised.encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, content in updates:
    backup = Path(str(path) + ".before_repair_" + stamp)
    shutil.copy2(path, backup)
    print(f"BACKUP: {backup}")
    path.write_bytes(content)
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_theta_hankel_basis_total_energy.sh
