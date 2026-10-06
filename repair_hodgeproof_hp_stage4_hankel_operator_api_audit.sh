#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import shutil

paths = [
    Path("HodgeProofHP/Stage4HankelOperatorApiAudit.lean"),
    Path("create_hodgeproof_hp_stage4_hankel_operator_api_audit.sh"),
]

old = "namespace HodgeProofHP\n"
new = "noncomputable section\n\nnamespace HodgeProofHP\n"
changes = []

for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")
    raw = path.read_bytes()
    text = raw.decode("utf-8").replace("\r\n", "\n")
    if text.count(old) != 1:
        raise SystemExit(f"STOP: expected one namespace match in {path}")
    if "noncomputable section" in text:
        raise SystemExit(f"STOP: already contains noncomputable section: {path}")
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

bash create_hodgeproof_hp_stage4_hankel_operator_api_audit.sh
