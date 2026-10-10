#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime

paths = [
    Path("HodgeProofHP/Stage4ThetaGaussianDerivatives.lean"),
    Path("create_hodgeproof_hp_stage4_theta_gaussian_derivatives.sh"),
]

replacements = [
(
"""  have hh := (hu.div_const 2).sub (he.const_mul a)
  convert hh.exp.const_mul 2 using 1 <;>
    dsimp only [hpThetaGaussianProfile] <;> ring
""",
"""  have hh := (hu.div_const 2).sub (he.const_mul a)
  change HasDerivAt
    (fun v : ℝ => v / 2 - a * Real.exp (2 * v))
    (1 / 2 - a * (Real.exp (2 * u) * (2 * 1))) u at hh
  have h := hh.exp.const_mul 2
  change HasDerivAt (hpThetaGaussianProfile a)
    (2 * (Real.exp (u / 2 - a * Real.exp (2 * u)) *
      (1 / 2 - a * (Real.exp (2 * u) * (2 * 1))))) u at h
  convert h using 1 <;>
    simp only [hpThetaGaussianProfile] <;> ring
"""
),
(
"""  convert hc.mul (hpThetaGaussianProfile_hasDerivAt a u)
    using 1 <;> ring
""",
"""  change HasDerivAt
    (fun v : ℝ => 1 / 2 - 2 * a * Real.exp (2 * v))
    (0 - (2 * a) * (Real.exp (2 * u) * (2 * 1))) u at hc
  convert hc.mul (hpThetaGaussianProfile_hasDerivAt a u)
    using 1 <;> ring
"""
),
(
"""  rw [hpThetaGaussianProfile_eq_product]
  unfold hpThetaGaussianParameter
  congr 1 <;> ring
""",
"""  rw [hpThetaGaussianProfile_eq_product]
  unfold hpThetaGaussianParameter
  have hex :
      -(Real.pi * ((n : ℝ) + 1) ^ 2) * Real.exp (2 * u) =
        -Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u) := by
    ring
  rw [hex]
  ring
"""
),
]

pending = []
for path in paths:
    original = path.read_bytes()
    updated = original.decode("utf-8")
    for old, new in replacements:
        count = updated.count(old)
        if count != 1:
            raise SystemExit(
                f"STOP: expected one matching proof in {path}, found {count}"
            )
        updated = updated.replace(old, new, 1)
    pending.append((path, original, updated.encode("utf-8")))

stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")

for path, original, updated in pending:
    backup = path.with_name(path.name + ".before_repair_" + stamp)
    backup.write_bytes(original)
    print(f"BACKUP: {backup}")

for path, original, updated in pending:
    path.write_bytes(updated)
    print(f"REPAIRED: {path}")
PY

bash create_hodgeproof_hp_stage4_theta_gaussian_derivatives.sh
