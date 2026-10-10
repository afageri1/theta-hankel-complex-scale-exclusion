#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import shutil

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelTranslation.lean"),
    Path("create_hodgeproof_hp_stage4_theta_hankel_translation.sh"),
]

replacements = [
    (
        """  have h :=
    (measurePreserving_add_left (volume : Measure ℝ) x).
      setLIntegral_comp_preimage
        (s := Set.Ioi x) measurableSet_Ioi hF
""",
        """  have h :=
    (measurePreserving_add_left (volume : Measure ℝ) x).setLIntegral_comp_preimage
      (s := Set.Ioi x) measurableSet_Ioi hF
"""
    ),
    (
        """  apply hpLIntegral_add_left_Ioi
  exact
    (hpRiemannThetaDifferentialKernel_continuous.pow 2).
      measurable.ennreal_ofReal
""",
        """  exact hpLIntegral_add_left_Ioi
    (fun u : ℝ =>
      ENNReal.ofReal (hpRiemannThetaDifferentialKernel u ^ 2))
    ((hpRiemannThetaDifferentialKernel_continuous.pow 2).measurable.ennreal_ofReal)
    x
"""
    ),
]

changes = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")
    raw = path.read_bytes()
    text = raw.decode("utf-8").replace("\r\n", "\n")
    for old, new in replacements:
        count = text.count(old)
        if count != 1:
            raise SystemExit(
                f"STOP: expected one match in {path}, found {count}"
            )
        text = text.replace(old, new, 1)
    if b"\r\n" in raw:
        text = text.replace("\n", "\r\n")
    changes.append((path, text.encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, _ in changes:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    shutil.copy2(path, backup)
    print(f"BACKUP: {backup}")

for path, content in changes:
    path.write_bytes(content)
    print(f"REPAIRED: {path}")
PY

lake env lean HodgeProofHP/Stage4ThetaHankelTranslation.lean
lake build HodgeProofHP.Stage4ThetaHankelTranslation

echo "PASS: Stage4ThetaHankelTranslation"
