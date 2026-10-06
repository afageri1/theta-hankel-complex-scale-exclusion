#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaHankelParseval.lean"),
    Path("create_hodgeproof_hp_stage4_theta_hankel_parseval.sh"),
]

old = "  simpa only [Complex.ofReal_pow] using h\n"
new = (
    "  convert! h using 1 <;>\n"
    "    simp only [Complex.ofReal_pow] <;> rfl\n"
)

pending = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")
    raw = path.read_bytes()
    text = raw.decode("utf-8").replace("\r\n", "\n")
    if text.count(old) != 1:
        raise SystemExit(f"STOP: expected exactly one matching proof: {path}")
    updated = text.replace(old, new, 1)
    if b"\r\n" in raw:
        updated = updated.replace("\n", "\r\n")
    pending.append((path, raw, updated.encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, raw, updated in pending:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(raw)
    path.write_bytes(updated)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

lake env lean HodgeProofHP/Stage4ThetaHankelParseval.lean
lake build HodgeProofHP.Stage4ThetaHankelParseval

printf '%s\n' 'PASS: Stage4ThetaHankelParseval'
