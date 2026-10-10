#!/usr/bin/env bash
set -euo pipefail

target="HodgeProofHP/Stage3GaussianExponentialBound.lean"
mkdir -p HodgeProofHP

if [ -f "$target" ]; then
  cp "$target" "${target}.before_exponential_bound"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage3GaussianWeightedMoments

/-! A Gaussian bound for exponential weights. -/

namespace HodgeProofHP

theorem hpGaussian_exponential_exponent_bound (a x : ℝ) :
    a * |x| - x ^ 2 / 2 ≤ a ^ 2 - x ^ 2 / 4 := by
  have hx : |x| ^ 2 = x ^ 2 := sq_abs x
  have hsq : 0 ≤ (|x| / 2 - a) ^ 2 :=
    sq_nonneg (|x| / 2 - a)
  nlinarith

theorem hpGaussian_exponential_weight_bound (a x : ℝ) :
    Real.exp (a * |x|) * Real.exp (-(x ^ 2 / 2)) ≤
      Real.exp (a ^ 2) * Real.exp (-(x ^ 2 / 4)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := hpGaussian_exponential_exponent_bound a x
  linarith

#print axioms hpGaussian_exponential_exponent_bound
#print axioms hpGaussian_exponential_weight_bound

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage3GaussianExponentialBound

python - <<'PY'
from pathlib import Path
import re

root = Path(".lake/packages/mathlib/Mathlib")
if not root.is_dir():
    raise SystemExit("STOP: mathlib source directory was not found")

groups = [
    (
        "GAUSSIAN INTEGRABILITY",
        root / "Analysis/SpecialFunctions",
        r"(?:theorem|lemma).*(?:integrable|memLp).*"
        r"(?:gaussian|exp_neg|exp_mul|sq)",
    ),
    (
        "L2 PRODUCTS AND DOMINATION",
        root / "MeasureTheory",
        r"(?:theorem|lemma).*(?:integrable_mul|"
        r"integrable_norm_rpow|memLp_norm_rpow|"
        r"integrable_sq|memLp_two|Integrable\.mono|"
        r"integrable_of_le|MemLp\.mono)",
    ),
    (
        "FOURIER UNIQUENESS AND AE INVERSION",
        root / "Analysis/Fourier",
        r"(?:theorem|lemma).*(?:injective|"
        r"fourier.*eq_zero|eq_zero.*fourier|"
        r"fourier.*eq.*ae|fourierInv.*eq.*ae|"
        r"ae.*fourier|fourier.*ae)",
    ),
]

for title, directory, pattern in groups:
    print(f"\n=== {title} ===")
    regex = re.compile(pattern)
    found = 0
    if directory.is_dir():
        for path in sorted(directory.rglob("*.lean")):
            lines = path.read_text(encoding="utf-8").splitlines()
            for i, line in enumerate(lines):
                if regex.search(line):
                    found += 1
                    print(f"\n{path}:{i + 1}")
                    print("\n".join(lines[max(0, i - 2):i + 12]))
    if not found:
        print("No matching declarations found by this targeted search.")
PY
