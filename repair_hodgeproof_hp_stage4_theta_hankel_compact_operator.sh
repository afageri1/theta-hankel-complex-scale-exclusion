#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelCompactOperator.lean"),
    Path("create_hodgeproof_hp_stage4_theta_hankel_compact_operator.sh"),
]

replacements = [
    (
        "simpa only [Real.sqrt_zero] using h",
        "simpa only [Function.comp_def, Real.sqrt_zero] using h",
    ),
    (
        """    (fun F => norm_nonneg
      (hpThetaHankelOperator -
        hpThetaHankelFiniteApproximation F))
    (fun F => hpThetaHankelOperator_sub_opNorm_le F)""",
        """    (Filter.Eventually.of_forall
      (fun F => norm_nonneg
        (hpThetaHankelOperator -
          hpThetaHankelFiniteApproximation F)))
    (Filter.Eventually.of_forall
      (fun F => hpThetaHankelOperator_sub_opNorm_le F))""",
    ),
]

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
updates = []

for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")
    raw = path.read_bytes()
    text = raw.decode("utf-8").replace("\r\n", "\n")
    for old, new in replacements:
        if text.count(old) != 1:
            raise SystemExit(f"STOP: expected one matching anchor: {path}")
        text = text.replace(old, new, 1)
    if b"\r\n" in raw:
        text = text.replace("\n", "\r\n")
    updates.append((path, raw, text.encode("utf-8")))

for path, raw, repaired in updates:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(raw)
    path.write_bytes(repaired)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_theta_hankel_compact_operator.sh
