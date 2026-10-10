#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import re

root = Path("HodgeProofHP")
paths = [
    (root / f"Stage4ThetaEnergyUpperIntegralBatch{b:02d}.lean", 20)
    for b in range(40)
]
creator = Path("create_hodgeproof_hp_stage4_theta_energy_finite_integral_upper.sh")
if creator.is_file():
    paths.append((creator, 1))

pattern = re.compile(
    r"^([ \t]*)exact (hpThetaEnergyUpper_interval_(?:\d+|\{i\}))"
    r" u hu\.1 hu\.2",
    re.MULTILINE,
)

def replacement(match):
    indent, name = match.groups()
    return (
        f"{indent}exact {name} u\n"
        f"{indent}  (by simpa only [zero_div, div_one] using hu.1)\n"
        f"{indent}  (by simpa only [zero_div, div_one] using hu.2)"
    )

updates = []
for path, expected in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing {path}; no files changed")
    with path.open("r", encoding="utf-8", newline="") as f:
        original = f.read()
    newline = "\r\n" if "\r\n" in original else "\n"
    text = original.replace("\r\n", "\n")
    count = len(list(pattern.finditer(text)))
    if count != expected:
        raise SystemExit(
            f"STOP: {path}: expected {expected} applications, found {count}; "
            "no files changed"
        )
    repaired = pattern.sub(replacement, text).replace("\n", newline)
    updates.append((path, original, repaired))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, original, repaired in updates:
    backup = path.with_name(path.name + ".before_endpoint_repair_" + stamp)
    with backup.open("w", encoding="utf-8", newline="") as f:
        f.write(original)
    with path.open("w", encoding="utf-8", newline="") as f:
        f.write(repaired)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

mkdir -p stage4_fourth_certificate_build_logs

for batch in $(seq 0 39); do
  tag=$(printf '%02d' "$batch")
  log="stage4_fourth_certificate_build_logs/energy_integral_batch_${tag}.log"
  printf '\n[%s] Building integral batch %s/39\n' "$(date +%H:%M:%S)" "$tag"

  if lake build "HodgeProofHP.Stage4ThetaEnergyUpperIntegralBatch${tag}" >"$log" 2>&1; then
    tail -n 12 "$log"
    printf 'PASS: energy integral batch %s\n' "$tag"
  else
    tail -n 100 "$log"
    printf 'STOP: integral batch %s failed; log: %s\n' "$tag" "$log"
    exit 1
  fi
done

log="stage4_fourth_certificate_build_logs/energy_finite_integral_upper.log"
if lake build HodgeProofHP.Stage4ThetaEnergyFiniteIntegralUpper >"$log" 2>&1; then
  tail -n 30 "$log"
  printf '%s\n' 'PASS: Stage4ThetaEnergyFiniteIntegralUpper'
else
  tail -n 100 "$log"
  printf 'STOP: final integral build failed; log: %s\n' "$log"
  exit 1
fi
