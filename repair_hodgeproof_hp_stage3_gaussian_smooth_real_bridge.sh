#!/usr/bin/env bash
set -euo pipefail

python3 - <<'PY'
from pathlib import Path
import re

paths = [
    Path("HodgeProofHP/Stage3GaussianSmooth.lean"),
    Path("create_hodgeproof_hp_stage3_gaussian_smooth.sh"),
]

replacement = """theorem hpGaussianGroundFunction_contDiff :
    ContDiff ℝ ∞ hpGaussianGroundFunction := by
  have hreal :
      ContDiff ℝ ∞
        (fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by
    fun_prop
  have hcomplex :
      ContDiff ℝ ∞
        (fun x : ℝ => (Real.exp (-(1 / 2 : ℝ) * x ^ 2) : ℂ)) := by
    have h := Complex.ofRealCLM.contDiff.comp hreal
    convert h using 1
    funext x
    simp
  have hfun :
      hpGaussianGroundFunction =
        (fun x : ℝ => (Real.exp (-(1 / 2 : ℝ) * x ^ 2) : ℂ)) := by
    funext x
    simp only [hpGaussianGroundFunction, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hfun]
  exact hcomplex

"""

pattern = re.compile(
    r"^theorem hpGaussianGroundFunction_contDiff :"
    r".*?(?=^#print axioms hpGaussianGroundFunction_contDiff)",
    re.MULTILINE | re.DOTALL,
)

updated = {}
for path in paths:
    if not path.is_file():
        raise SystemExit(f"STOP: missing {path}")
    revised, count = pattern.subn(
        replacement, path.read_text(encoding="utf-8")
    )
    if count != 1:
        raise SystemExit(f"STOP: expected one theorem in {path}; found {count}")
    updated[path] = revised

for path, source in updated.items():
    path.write_text(source, encoding="utf-8")
    print(f"UPDATED: {path}")
PY

lake env lean HodgeProofHP/Stage3GaussianSmooth.lean
lake build HodgeProofHP.Stage3GaussianSmooth
