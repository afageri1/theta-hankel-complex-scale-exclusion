#!/usr/bin/env bash
set -euo pipefail

python3 - <<'PY'
from pathlib import Path

paths = [
    Path("HodgeProofHP/Stage3GaussianSmooth.lean"),
    Path("create_hodgeproof_hp_stage3_gaussian_smooth.sh"),
]

old = """theorem hpGaussianGroundFunction_contDiff :
    ContDiff ℝ ∞ hpGaussianGroundFunction := by
  unfold hpGaussianGroundFunction
  fun_prop"""

new = """theorem hpGaussianGroundFunction_contDiff :
    ContDiff ℝ ∞ hpGaussianGroundFunction := by
  have hcast : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := by
    simpa only [Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.contDiff :
        ContDiff ℝ ∞ (Complex.ofRealCLM : ℝ → ℂ))
  have harg :
      ContDiff ℝ ∞ (fun x : ℝ => -(1 / 2 : ℂ) * (x : ℂ) ^ 2) := by
    exact contDiff_const.mul (hcast.pow 2)
  simpa only [hpGaussianGroundFunction] using harg.cexp"""

updated = {}
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing {path}")
    source = path.read_text(encoding="utf-8")
    if source.count(old) != 1:
        raise SystemExit(f"STOP: expected one matching proof in {path}")
    updated[path] = source.replace(old, new)

for path, source in updated.items():
    path.write_text(source, encoding="utf-8")
    print(f"UPDATED: {path}")
PY

lake env lean HodgeProofHP/Stage3GaussianSmooth.lean
lake build HodgeProofHP.Stage3GaussianSmooth
