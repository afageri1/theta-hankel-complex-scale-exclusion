#!/usr/bin/env bash
set -euo pipefail

target="HodgeProofHP/Stage3GaussianMomentTaylorIntegrals.lean"

if [ -f "$target" ]; then
  cp "$target" "${target}.before_taylor_integrals"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage3GaussianWeightedExponentialL1

/-! Vanishing integrals of finite exponential Taylor sums. -/

open MeasureTheory
open scoped BigOperators

namespace HodgeProofHP

noncomputable def hpGaussianMomentTaylorTerm
    (v : HPSpace) (z : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  (z ^ n / (n.factorial : ℂ)) *
    ((x : ℂ) ^ n * hpGaussianWeightedL2Function v x)

theorem hpGaussianMomentTaylorTerm_integrable
    (v : HPSpace) (z : ℂ) (n : ℕ) :
    Integrable (hpGaussianMomentTaylorTerm v z n) volume := by
  exact
    (hpGaussianWeightedL2Function_moment_integrable v n).const_mul
      (z ^ n / (n.factorial : ℂ))

theorem hpGaussianMomentTaylorTerm_integral_eq_zero
    (v : HPSpace) (hv : v ∈ hpHermiteL2Span.orthogonal)
    (z : ℂ) (n : ℕ) :
    (∫ x : ℝ, hpGaussianMomentTaylorTerm v z n x) = 0 := by
  unfold hpGaussianMomentTaylorTerm
  rw [integral_const_mul,
    hpGaussianWeightedL2Function_moment_eq_zero v hv n, mul_zero]

theorem hpGaussianMomentTaylorSum_integral_eq_zero
    (v : HPSpace) (hv : v ∈ hpHermiteL2Span.orthogonal)
    (z : ℂ) (N : ℕ) :
    (∫ x : ℝ,
      ∑ n ∈ Finset.range N, hpGaussianMomentTaylorTerm v z n x) = 0 := by
  rw [integral_finset_sum (Finset.range N)
    (fun n _ => hpGaussianMomentTaylorTerm_integrable v z n)]
  simp only [hpGaussianMomentTaylorTerm_integral_eq_zero v hv,
    Finset.sum_const_zero]

#print axioms hpGaussianMomentTaylorTerm_integrable
#print axioms hpGaussianMomentTaylorTerm_integral_eq_zero
#print axioms hpGaussianMomentTaylorSum_integral_eq_zero

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage3GaussianMomentTaylorIntegrals

python - <<'PY'
from pathlib import Path
import re

root = Path(".lake/packages/mathlib/Mathlib")
jobs = [
    (
        "EXPONENTIAL SERIES",
        root / "Analysis",
        r"(?:theorem|lemma)\s+(?:Complex\.|Real\.)?"
        r"(?:hasSum_exp|exp_eq_tsum|summable_pow_div_factorial)"
    ),
    (
        "DOMINATED CONVERGENCE",
        root / "MeasureTheory/Integral",
        r"(?:theorem|lemma)\s+"
        r"(?:tendsto_integral_of_dominated_convergence|"
        r"hasSum_integral_of_dominated_convergence|"
        r"integral_tsum_of_summable_integral_norm)"
    ),
]

for title, directory, pattern in jobs:
    print(f"\n=== {title} ===")
    regex = re.compile(pattern)
    found = False
    for path in sorted(directory.rglob("*.lean")):
        lines = path.read_text(encoding="utf-8").splitlines()
        for i, line in enumerate(lines):
            if regex.search(line):
                found = True
                print(f"\n{path}:{i + 1}")
                print("\n".join(lines[max(0, i - 3):i + 24]))
    if not found:
        print("No matching declarations found by this targeted search.")
PY
