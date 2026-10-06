#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4RiemannXiLogIntegral.lean"),
    Path("create_hodgeproof_hp_stage4_riemann_xi_log_integral.sh"),
]
replacements = [
    (
        "rw [integral_const_smul]",
        "rw [integral_smul]",
    ),
    (
        "simpa only [mul_smul] using hd.const_smul (2 : ℝ)",
        "simpa only [mul_smul] using "
        "(MeasureTheory.Integrable.fun_smul (2 : ℝ) hd)",
    ),
]
prepared = []

for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")

    original = path.read_bytes()
    text = original.decode("utf-8")

    for old, new in replacements:
        if text.count(old) != 1:
            raise SystemExit(
                f"STOP: expected one occurrence of {old!r} in {path}. "
                "No files changed."
            )
        text = text.replace(old, new)

    prepared.append((path, original, text.encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")

for path, original, updated in prepared:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(original)
    print(f"BACKUP: {backup}")

for path, original, updated in prepared:
    path.write_bytes(updated)
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_riemann_xi_log_integral.sh
