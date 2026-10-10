#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path

paths = [
    Path("HodgeProofHP/Stage3GaussianExponentialIntegrability.lean"),
    Path("create_hodgeproof_hp_stage3_gaussian_exponential_integrability.sh"),
]

old = """    simpa only [smul_eq_mul] using
      hpQuarterGaussian_memLp.const_smul (Real.exp (a ^ 2))"""

new = """    have h :=
      hpQuarterGaussian_memLp.const_smul (Real.exp (a ^ 2))
    change MemLp
      (fun x : ℝ =>
        Real.exp (a ^ 2) * Real.exp (-(x ^ 2 / 4)))
      2 volume at h
    exact h"""

updates = []
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing file: {path}")
    text = path.read_text(encoding="utf-8")
    if new in text:
        print(f"Already repaired: {path}")
        continue
    if text.count(old) != 1:
        raise SystemExit(f"STOP: expected exactly one matching block: {path}")
    updates.append((path, text))

for path, text in updates:
    backup = Path(str(path) + ".before_pointwise_smul_fix")
    if not backup.exists():
        backup.write_text(text, encoding="utf-8")
    path.write_text(text.replace(old, new, 1), encoding="utf-8")
    print(f"Repaired: {path}")
PY

lake env lean HodgeProofHP/Stage3GaussianExponentialIntegrability.lean
lake build HodgeProofHP.Stage3GaussianExponentialIntegrability
