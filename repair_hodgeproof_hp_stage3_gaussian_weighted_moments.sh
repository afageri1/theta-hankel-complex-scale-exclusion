#!/usr/bin/env bash
set -euo pipefail

python - <<'PY'
from pathlib import Path

targets = [
    Path("HodgeProofHP/Stage3GaussianWeightedMoments.lean"),
    Path("create_hodgeproof_hp_stage3_gaussian_weighted_moments.sh"),
]

changes = [
    (
"""  simp [RCLike.inner_apply', hpGaussianGroundFunction_eq_real,
    mul_assoc]""",
"""  have hx : (starRingEnd ℂ) (x : ℂ) = (x : ℂ) :=
    Complex.conj_ofReal x
  have hg :
      (starRingEnd ℂ) (hpGaussianGroundFunction x) =
        hpGaussianGroundFunction x := by
    rw [hpGaussianGroundFunction_eq_real]
    exact Complex.conj_ofReal _
  rw [RCLike.inner_apply', map_mul, map_pow, hx, hg]
  ring"""
    ),
    (
"""  simpa [hpGaussianWeightedL2Function] using
    hpPolynomialGaussian_mul_L2_integrable
      (1 : Polynomial ℂ) v""",
"""  change Integrable
    (fun x : ℝ => hpGaussianGroundFunction x * v x) volume
  simpa only [Polynomial.eval_one, one_mul] using
    hpPolynomialGaussian_mul_L2_integrable
      (1 : Polynomial ℂ) v"""
    ),
]

for path in targets:
    original = path.read_text(encoding="utf-8")
    text = original
    for old, new in changes:
        if new in text:
            continue
        if text.count(old) != 1:
            raise SystemExit(f"STOP: expected exactly one matching block in {path}")
        text = text.replace(old, new, 1)
    if text != original:
        backup = Path(str(path) + ".before_conjugate_integrable_fix")
        if not backup.exists():
            backup.write_text(original, encoding="utf-8")
        path.write_text(text, encoding="utf-8")
    print(f"Repaired or already current: {path}")
PY

lake env lean HodgeProofHP/Stage3GaussianWeightedMoments.lean
lake build HodgeProofHP.Stage3GaussianWeightedMoments
