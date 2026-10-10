#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path
from datetime import datetime
import shutil

paths = [
    Path("HodgeProofHP/Stage3GaussianWeightedL2.lean"),
    Path("create_hodgeproof_hp_stage3_gaussian_weighted_l2.sh"),
]

replacements = [
    (
"""  have hc : Continuous hpGaussianGroundFunction := by
    simp only [hpGaussianGroundFunction_eq_real]
    fun_prop""",
"""  have hc : Continuous hpGaussianGroundFunction := by
    have heq : hpGaussianGroundFunction =
        (fun x : ℝ => (Real.exp (-(x ^ 2 / 2)) : ℂ)) := by
      funext x
      exact hpGaussianGroundFunction_eq_real x
    rw [heq]
    fun_prop"""
    ),
    (
"""  exact hv.trans (Lp.coeFn_zero ℂ 2 volume).symm""",
"""  filter_upwards [hv, Lp.coeFn_zero ℂ 2 volume] with x hx hz
  exact hx.trans hz.symm"""
    ),
]

stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
updates = []

for path in paths:
    text = path.read_text(encoding="utf-8")
    for old, new in replacements:
        if old in text:
            text = text.replace(old, new)
        elif new not in text:
            raise SystemExit(f"STOP: expected proof not found in {path}")
    updates.append((path, text))

for path, text in updates:
    shutil.copy2(path, str(path) + ".bak." + stamp)
    path.write_text(text, encoding="utf-8")
    print(f"Repaired: {path}")
PY

bash create_hodgeproof_hp_stage3_gaussian_weighted_l2.sh
