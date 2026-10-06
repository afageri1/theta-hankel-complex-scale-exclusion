#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelSpectralCompleteness.lean"),
    Path("create_hodgeproof_hp_stage4_theta_hankel_spectral_completeness.sh"),
]

replacements = [
    (
"""  have hclosure :=
    (Submodule.span ℂ
      (Set.range ⇑(hpThetaHankelEigenspaceBasis ev)))
        .topologicalClosure_minimal hspan hclosed""",
"""  have hclosure :=
    Submodule.topologicalClosure_minimal
      (Submodule.span ℂ
        (Set.range ⇑(hpThetaHankelEigenspaceBasis ev)))
      hspan hclosed"""
    ),
    (
"""    exact Submodule.mem_iInf.mpr heigenspaces""",
"""    simpa using heigenspaces"""
    ),
]

updates = []
for path in paths:
    original = path.read_bytes()
    text = original.decode("utf-8")
    newline = "\r\n" if "\r\n" in text else "\n"
    for old, new in replacements:
        old = old.replace("\n", newline)
        new = new.replace("\n", newline)
        if text.count(old) != 1:
            raise SystemExit(f"STOP: {path}: expected exactly one matching block")
        text = text.replace(old, new, 1)
    updates.append((path, original, text.encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, original, repaired in updates:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(original)
    path.write_bytes(repaired)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_theta_hankel_spectral_completeness.sh
