#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaSecondLocalBound.lean"),
    Path("create_hodgeproof_hp_stage4_theta_second_local_bound.sh"),
]

old = """  simpa only [hpThetaGaussianFirstTerm, hpThetaGaussianSecondTerm] using
    hpThetaGaussianProfile_first_hasDerivAt
      (hpThetaGaussianParameter n) u"""

new = """  change HasDerivAt
    (fun v : ℝ =>
      ((1 / 2 : ℝ) -
        2 * hpThetaGaussianParameter n * Real.exp (2 * v)) *
      hpThetaGaussianProfile (hpThetaGaussianParameter n) v)
    ((((1 / 2 : ℝ) -
        2 * hpThetaGaussianParameter n * Real.exp (2 * u)) ^ 2 -
        4 * hpThetaGaussianParameter n * Real.exp (2 * u)) *
      hpThetaGaussianProfile (hpThetaGaussianParameter n) u)
    u
  exact hpThetaGaussianProfile_first_hasDerivAt
    (hpThetaGaussianParameter n) u"""

updates = []
for path in paths:
    raw = path.read_bytes()
    text = raw.decode("utf-8")
    newline = "\r\n" if "\r\n" in text else "\n"
    normalized = text.replace("\r\n", "\n")
    count = normalized.count(old)
    if count != 1:
        raise SystemExit(
            f"STOP: {path}: expected one matching proof, found {count}"
        )
    updated = normalized.replace(old, new)
    updates.append((path, raw, updated.replace("\n", newline).encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, raw, updated in updates:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(raw)
    print(f"BACKUP: {backup}")

for path, raw, updated in updates:
    path.write_bytes(updated)
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_theta_second_local_bound.sh
