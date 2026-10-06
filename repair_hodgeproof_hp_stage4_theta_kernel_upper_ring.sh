#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [Path("HodgeProofHP/Stage4ThetaKernelFirstTermUpper.lean")]
creator = Path("create_hodgeproof_hp_stage4_theta_kernel_first_term_upper.sh")
if creator.is_file():
    paths.append(creator)

old = "convert h using 1 <;> dsimp [m] <;> ring"
new = "convert h using 1 <;> (try dsimp [m]) <;> ring"

updates = []
for path in paths:
    with path.open("r", encoding="utf-8", newline="") as f:
        text = f.read()
    if text.count(old) != 1:
        raise SystemExit(
            f"STOP: {path}: expected one matching line; no files changed"
        )
    updates.append((path, text, text.replace(old, new)))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, original, repaired in updates:
    backup = path.with_name(path.name + ".before_ring_repair_" + stamp)
    with backup.open("w", encoding="utf-8", newline="") as f:
        f.write(original)
    with path.open("w", encoding="utf-8", newline="") as f:
        f.write(repaired)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

mkdir -p stage4_fourth_certificate_build_logs
log="stage4_fourth_certificate_build_logs/kernel_upper_ring_repair.log"

if lake build HodgeProofHP.Stage4ThetaKernelFirstTermUpper >"$log" 2>&1; then
  tail -n 35 "$log"
  printf '%s\n' 'PASS: Stage4ThetaKernelFirstTermUpper'
else
  tail -n 100 "$log"
  printf 'STOP: build failed; log: %s\n' "$log"
  exit 1
fi
