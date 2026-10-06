#!/usr/bin/env bash
set -euo pipefail

target="HodgeProofHP/Stage3GaussianTaylorDomination.lean"

if [ -f "$target" ]; then
  cp "$target" "${target}.before_taylor_domination"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage3GaussianMomentTaylorIntegrals

/-! An integrable bound for all Gaussian-weighted Taylor partial sums. -/

open MeasureTheory
open scoped BigOperators

namespace HodgeProofHP

theorem hpGaussianMomentTaylorTerm_norm
    (v : HPSpace) (z : ℂ) (n : ℕ) (x : ℝ) :
    ‖hpGaussianMomentTaylorTerm v z n x‖ =
      ((‖z‖ * |x|) ^ n / (n.factorial : ℝ)) *
        ‖hpGaussianWeightedL2Function v x‖ := by
  simp [hpGaussianMomentTaylorTerm, norm_mul, norm_div, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm]

theorem hpGaussianMomentTaylorSum_norm_le
    (v : HPSpace) (z : ℂ) (N : ℕ) (x : ℝ) :
    ‖∑ n ∈ Finset.range N, hpGaussianMomentTaylorTerm v z n x‖ ≤
      Real.exp (‖z‖ * |x|) *
        ‖hpGaussianWeightedL2Function v x‖ := by
  calc
    ‖∑ n ∈ Finset.range N, hpGaussianMomentTaylorTerm v z n x‖
        ≤ ∑ n ∈ Finset.range N,
            ‖hpGaussianMomentTaylorTerm v z n x‖ :=
      norm_sum_le _ _
    _ = ∑ n ∈ Finset.range N,
          ((‖z‖ * |x|) ^ n / (n.factorial : ℝ)) *
            ‖hpGaussianWeightedL2Function v x‖ := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hpGaussianMomentTaylorTerm_norm v z n x
    _ = (∑ n ∈ Finset.range N,
          (‖z‖ * |x|) ^ n / (n.factorial : ℝ)) *
            ‖hpGaussianWeightedL2Function v x‖ := by
      rw [Finset.sum_mul]
    _ ≤ Real.exp (‖z‖ * |x|) *
          ‖hpGaussianWeightedL2Function v x‖ :=
      mul_le_mul_of_nonneg_right
        (Real.sum_le_exp_of_nonneg
          (mul_nonneg (norm_nonneg z) (abs_nonneg x)) N)
        (norm_nonneg _)

theorem hpGaussianMomentTaylorSum_bound_integrable
    (v : HPSpace) (z : ℂ) :
    Integrable
      (fun x : ℝ =>
        Real.exp (‖z‖ * |x|) *
          ‖hpGaussianWeightedL2Function v x‖)
      volume :=
  hpGaussianWeightedL2Function_exponential_norm_integrable ‖z‖ v

#print axioms hpGaussianMomentTaylorTerm_norm
#print axioms hpGaussianMomentTaylorSum_norm_le
#print axioms hpGaussianMomentTaylorSum_bound_integrable

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage3GaussianTaylorDomination

python - <<'PY'
from pathlib import Path
import re

root = Path(".lake/packages/mathlib/Mathlib/Analysis")
pattern = re.compile(
    r"(?:theorem|lemma)\s+\S*(?:"
    r"hasSum\S*exp|exp\S*hasSum|"
    r"tendsto\S*exp|exp\S*tendsto)"
)

print("\n=== EXPONENTIAL SERIES CONVERGENCE ===")
found = False
for path in sorted(root.rglob("*.lean")):
    if "Exp" not in path.name and "Complex" not in path.parts:
        continue
    lines = path.read_text(encoding="utf-8").splitlines()
    for i, line in enumerate(lines):
        if pattern.search(line):
            found = True
            print(f"\n{path}:{i + 1}")
            print("\n".join(lines[max(0, i - 2):i + 16]))
if not found:
    print("No matching declarations found by this targeted search.")
PY
