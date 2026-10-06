#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaComplexDerivatives.lean"),
    Path("create_hodgeproof_hp_stage4_theta_complex_derivatives.sh"),
]

changes = [
    (
        "(deriv hpRiemannThetaLogProfile u : ℂ)",
        "((deriv hpRiemannThetaLogProfile u : ℝ) : ℂ)",
        1,
    ),
    (
        "(deriv hpRiemannThetaLogProfile x : ℂ)",
        "((deriv hpRiemannThetaLogProfile x : ℝ) : ℂ)",
        1,
    ),
    (
        "(deriv (deriv hpRiemannThetaLogProfile) u : ℂ)",
        "((deriv (deriv hpRiemannThetaLogProfile) u : ℝ) : ℂ)",
        1,
    ),
    (
        "    simpa only [mul_one] using\n",
        "    simpa using\n",
        2,
    ),
    (
        "  simpa only [Function.comp_def, neg_mul, mul_comm] using\n"
        "    (Complex.hasDerivAt_cos (z * (u : ℂ))).comp u harg\n",
        "  convert (Complex.hasDerivAt_cos (z * (u : ℂ))).comp u harg "
        "using 1 <;>\n"
        "    ring\n",
        1,
    ),
]

prepared = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")
    raw = path.read_bytes()
    text = raw.decode("utf-8").replace("\r\n", "\n")
    for old, new, expected in changes:
        count = text.count(old)
        if count != expected:
            raise SystemExit(
                f"STOP: {path}: expected {expected} matches; found {count}"
                f"\nTarget: {old}"
            )
        text = text.replace(old, new)
    if b"\r\n" in raw:
        text = text.replace("\n", "\r\n")
    prepared.append((path, raw, text.encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, raw, _ in prepared:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(raw)
    print(f"BACKUP: {backup}")

for path, _, fixed in prepared:
    path.write_bytes(fixed)
    print(f"REPAIRED: {path}")
PY

lake env lean HodgeProofHP/Stage4ThetaComplexDerivatives.lean
lake build HodgeProofHP.Stage4ThetaComplexDerivatives
