#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage3ClosureShiftedSurjective.lean"),
    Path("create_hodgeproof_hp_stage3_closure_shifted_surjective.sh"),
]

old = "    rw [hx1, hx2]"
new = """    change HPHarmonicClosure.toFun x =
      (p : HPSpace × HPSpace).2 at hx2
    rw [hx1, hx2]"""

pending = []
for path in paths:
    original = path.read_text(encoding="utf-8")
    if original.count(old) != 1:
        raise SystemExit(f"STOP: expected exactly one matching block in {path}")
    pending.append((path, original, original.replace(old, new, 1)))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, original, updated in pending:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_text(original, encoding="utf-8")
    path.write_text(updated, encoding="utf-8")
    print(f"Repaired: {path}")
    print(f"Backup: {backup}")
PY

bash ./create_hodgeproof_hp_stage3_closure_shifted_surjective.sh
