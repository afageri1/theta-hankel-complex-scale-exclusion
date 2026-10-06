#!/usr/bin/env bash
set -euo pipefail

python3 - <<'PY'
from pathlib import Path
import re

files = [
    Path("HodgeProofHP/Stage3ComplexGaussianBound.lean"),
    Path("create_hodgeproof_hp_stage3_complex_gaussian_bound.sh"),
]

replacement = """theorem hpGaussianGroundFunction_weighted_bounded (k : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ,
      ‖x‖ ^ k * ‖hpGaussianGroundFunction x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hpRealGaussian_weighted_bounded k
  refine ⟨C, fun x => ?_⟩
  have hnorm :
      ‖hpGaussianGroundFunction x‖ =
        Real.exp (-(1 / 2 : ℝ) * x ^ 2) := by
    change ‖Complex.exp (-((1 / 2 : ℂ) * (x : ℂ) ^ 2))‖ = _
    rw [show -((1 / 2 : ℂ) * (x : ℂ) ^ 2) =
        -(1 / 2 : ℂ) * (x : ℂ) ^ 2 by ring,
      norm_cexp_neg_mul_sq]
    norm_num
  simpa only [Real.norm_eq_abs, hnorm] using hC x

"""

pattern = re.compile(
    r"^theorem hpGaussianGroundFunction_weighted_bounded \(k : ℕ\) :"
    r".*?(?=^#print axioms hpGaussianGroundFunction_weighted_bounded)",
    re.MULTILINE | re.DOTALL,
)

updated = {}
for path in files:
    if not path.is_file():
        raise SystemExit(f"STOP: missing {path}")
    revised, count = pattern.subn(
        replacement, path.read_text(encoding="utf-8")
    )
    if count != 1:
        raise SystemExit(f"STOP: expected one theorem in {path}; found {count}")
    updated[path] = revised

for path, contents in updated.items():
    path.write_text(contents, encoding="utf-8")
    print(f"UPDATED: {path}")
PY

lake env lean HodgeProofHP/Stage3ComplexGaussianBound.lean
lake build HodgeProofHP.Stage3ComplexGaussianBound
