#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path

paths = [
    Path("HodgeProofHP/Stage3GaussianWeightedExponentialL1.lean"),
    Path("create_hodgeproof_hp_stage3_gaussian_weighted_exponential_l1.sh"),
]

old = """    simpa only [hpGaussianWeightedL2Function, mul_assoc] using
      hc.aestronglyMeasurable.mul
        (MeasureTheory.Lp.memLp v).aestronglyMeasurable"""

new = """    have h :=
      hc.aestronglyMeasurable.mul
        (MeasureTheory.Lp.memLp v).aestronglyMeasurable
    change AEStronglyMeasurable
      (fun x : ℝ =>
        ((Real.exp (a * |x|) : ℂ) *
          hpGaussianGroundFunction x) * v x)
      volume at h
    simpa only [hpGaussianWeightedL2Function, mul_assoc] using h"""

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
    backup = Path(str(path) + ".before_pointwise_measurability_fix")
    if not backup.exists():
        backup.write_text(text, encoding="utf-8")
    path.write_text(text.replace(old, new, 1), encoding="utf-8")
    print(f"Repaired: {path}")
PY

lake env lean HodgeProofHP/Stage3GaussianWeightedExponentialL1.lean
lake build HodgeProofHP.Stage3GaussianWeightedExponentialL1
