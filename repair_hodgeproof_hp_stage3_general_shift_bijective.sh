#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import shutil

paths = [
    Path("HodgeProofHP/Stage3GeneralShiftBijective.lean"),
    Path("create_hodgeproof_hp_stage3_general_shift_bijective.sh"),
]

old = """    have heq : T v = v := by
      simpa only [one_smul] using hv.apply_eq_smul
"""

new = """    have heq : T v = v := by
      have happly : T.toLinearMap v = (1 : ℂ) • v :=
        hv.apply_eq_smul
      change T v = (1 : ℂ) • v at happly
      rw [one_smul] at happly
      exact happly
"""

prepared = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")
    content = path.read_bytes().decode("utf-8")
    newline = "\r\n" if "\r\n" in content else "\n"
    needle = old.replace("\n", newline)
    replacement = new.replace("\n", newline)
    count = content.count(needle)
    if count != 1:
        raise SystemExit(
            f"STOP: expected exactly one matching block in {path}; found {count}"
        )
    prepared.append((path, content.replace(needle, replacement, 1)))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, _ in prepared:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    shutil.copy2(path, backup)
    print(f"BACKUP: {backup}")

for path, content in prepared:
    path.write_bytes(content.encode("utf-8"))
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage3_general_shift_bijective.sh
