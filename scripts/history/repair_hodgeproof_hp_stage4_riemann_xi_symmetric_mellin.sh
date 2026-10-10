#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4RiemannXiSymmetricMellin.lean"),
    Path("create_hodgeproof_hp_stage4_riemann_xi_symmetric_mellin.sh"),
]
old = "  exact lt_trans zero_lt_one hx"
prepared = []

for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")

    original = path.read_bytes()
    text = original.decode("utf-8")
    newline = "\r\n" if "\r\n" in text else "\n"

    if text.count(old) != 1:
        raise SystemExit(
            f"STOP: expected one matching line in {path}. "
            "No files changed."
        )

    new = newline.join([
        "  change (0 : ℝ) < x",
        "  change (1 : ℝ) < x at hx",
        "  linarith",
    ])
    prepared.append((path, original, text.replace(old, new).encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")

for path, original, updated in prepared:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(original)
    print(f"BACKUP: {backup}")

for path, original, updated in prepared:
    path.write_bytes(updated)
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_riemann_xi_symmetric_mellin.sh
