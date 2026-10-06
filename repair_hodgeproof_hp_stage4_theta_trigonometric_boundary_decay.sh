#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaTrigonometricBoundaryDecay.lean"),
    Path("create_hodgeproof_hp_stage4_theta_trigonometric_boundary_decay.sh"),
]

replacements = [
    ("    dsimp only\n", "", 2),
    (
        "(deriv hpRiemannThetaLogProfile u : ℂ)",
        "((deriv hpRiemannThetaLogProfile u : ℝ) : ℂ)",
        2,
    ),
    (
        "    simp [norm_mul, Complex.norm_exp, Real.norm_eq_abs,\n"
        "      abs_of_pos (Real.exp_pos (a.re * u)), mul_comm]",
        "    simp [norm_mul, Complex.norm_exp, Real.norm_eq_abs, mul_comm]",
        1,
    ),
]

prepared = []
for path in paths:
    raw = path.read_bytes()
    text = raw.decode("utf-8")
    newline = "\r\n" if "\r\n" in text else "\n"
    text = text.replace("\r\n", "\n")
    for old, new, expected in replacements:
        count = text.count(old)
        if count != expected:
            raise SystemExit(
                f"STOP: {path}: expected {expected} occurrences, found {count}"
            )
        text = text.replace(old, new)
    prepared.append((path, raw, text.replace("\n", newline).encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, raw, _ in prepared:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(raw)
    print("BACKUP:", backup)

for path, _, updated in prepared:
    path.write_bytes(updated)
    print("REPAIRED:", path)
PY

bash create_hodgeproof_hp_stage4_theta_trigonometric_boundary_decay.sh
