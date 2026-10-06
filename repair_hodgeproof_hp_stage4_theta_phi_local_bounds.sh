#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaPhiLocalBounds.lean"),
    Path("create_hodgeproof_hp_stage4_theta_phi_local_bounds.sh"),
]

replacements = [
(
"""  simp only [hpThetaPhiCosIntegrandFirst, norm_mul, norm_neg,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
  calc
    |hpRiemannThetaDifferentialKernel u| * u *
        ‖Complex.sin (z * (u : ℂ))‖
        ≤""",
"""  calc
    ‖hpThetaPhiCosIntegrandFirst z u‖ =
        |hpRiemannThetaDifferentialKernel u| * u *
          ‖Complex.sin (z * (u : ℂ))‖ := by
      simp only [hpThetaPhiCosIntegrandFirst, norm_mul, norm_neg,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
    _ ≤"""
),
(
"""    _ = |u * Real.exp (c * u) *
          hpRiemannThetaDifferentialKernel u| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hu,""",
"""    _ = ‖u * Real.exp (c * u) *
          hpRiemannThetaDifferentialKernel u‖ := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hu,"""
),
(
"""  simp only [hpThetaPhiCosIntegrandSecond, norm_mul, norm_neg,
    norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hu]
  calc
    |hpRiemannThetaDifferentialKernel u| * u ^ 2 *
        ‖Complex.cos (z * (u : ℂ))‖
        ≤""",
"""  calc
    ‖hpThetaPhiCosIntegrandSecond z u‖ =
        |hpRiemannThetaDifferentialKernel u| * u ^ 2 *
          ‖Complex.cos (z * (u : ℂ))‖ := by
      simp only [hpThetaPhiCosIntegrandSecond, norm_mul, norm_neg,
        norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hu]
    _ ≤"""
),
(
"""    _ = |u ^ 2 * Real.exp (c * u) *
          hpRiemannThetaDifferentialKernel u| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg u),""",
"""    _ = ‖u ^ 2 * Real.exp (c * u) *
          hpRiemannThetaDifferentialKernel u‖ := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (sq_nonneg u),"""
),
]

prepared = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing {path}")
    raw = path.read_bytes()
    text = raw.decode("utf-8").replace("\r\n", "\n")
    for old, new in replacements:
        count = text.count(old)
        if count != 1:
            raise SystemExit(
                f"STOP: expected one matching block in {path}, found {count}"
            )
        text = text.replace(old, new, 1)
    if b"\r\n" in raw:
        text = text.replace("\n", "\r\n")
    prepared.append((path, raw, text.encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
for path, raw, updated in prepared:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(raw)
    path.write_bytes(updated)
    print(f"BACKUP: {backup}")
    print(f"REPAIRED: {path}")
PY

lake env lean HodgeProofHP/Stage4ThetaPhiLocalBounds.lean
lake build HodgeProofHP.Stage4ThetaPhiLocalBounds
echo "PASS: Stage4ThetaPhiLocalBounds"
