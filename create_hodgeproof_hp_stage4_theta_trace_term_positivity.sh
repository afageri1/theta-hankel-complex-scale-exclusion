#!/usr/bin/env bash
set -euo pipefail

if [[ ! -f lakefile.lean && ! -f lakefile.toml ]]; then
  echo "STOP: run from the hodgeproof-hp repository root."
  exit 1
fi

lake build HodgeProofHP.Stage4ThetaFirstTraceXiRatio

target="HodgeProofHP/Stage4ThetaTraceTermPositivity.lean"
mkdir -p HodgeProofHP

if [[ -f "$target" ]]; then
  backup="${target}.before_update_$(date +%Y%m%d_%H%M%S)_$$"
  cp "$target" "$backup"
  echo "BACKUP: $backup"
fi

cat > "$target" <<'LEAN'
import HodgeProofHP.Stage4ThetaFirstTraceXiRatio

/-!
Positivity of the polynomial factor in the theta differential series.
Print the exact existing series definitions for the next comparison step.
-/

noncomputable section

namespace HodgeProofHP

theorem hpThetaTrace_polynomial_pos
    (a x : ℝ) (ha : 3 ≤ a) (hx : 1 ≤ x) :
    0 < 4 * a ^ 2 * x ^ 2 - 6 * a * x := by
  have ha0 : 0 ≤ a := by linarith
  have hax : a ≤ a * x := by
    simpa using mul_le_mul_of_nonneg_left hx ha0
  have hp : 0 < a * x := by linarith
  have hq : 0 < 4 * (a * x) - 6 := by linarith
  calc
    0 < (a * x) * (4 * (a * x) - 6) := mul_pos hp hq
    _ = 4 * a ^ 2 * x ^ 2 - 6 * a * x := by ring

theorem hpThetaTrace_exp_polynomial_pos
    (a u : ℝ) (ha : 3 ≤ a) (hu : 0 ≤ u) :
    0 < 4 * a ^ 2 * Real.exp (4 * u) -
      6 * a * Real.exp (2 * u) := by
  have hx : 1 ≤ Real.exp (2 * u) := by
    have h := Real.add_one_le_exp (2 * u)
    linarith
  have hexp :
      Real.exp (4 * u) = Real.exp (2 * u) ^ 2 := by
    calc
      Real.exp (4 * u) =
          Real.exp (2 * u + 2 * u) := by congr 1 <;> ring
      _ = Real.exp (2 * u) * Real.exp (2 * u) :=
        Real.exp_add _ _
      _ = Real.exp (2 * u) ^ 2 := by ring
  rw [hexp]
  exact hpThetaTrace_polynomial_pos a (Real.exp (2 * u)) ha hx

theorem hpThetaTrace_exp_weighted_term_pos
    (a u : ℝ) (ha : 3 ≤ a) (hu : 0 ≤ u) :
    0 <
      (4 * a ^ 2 * Real.exp (4 * u) -
        6 * a * Real.exp (2 * u)) *
      Real.exp (u / 2 - a * Real.exp (2 * u)) := by
  exact mul_pos
    (hpThetaTrace_exp_polynomial_pos a u ha hu)
    (Real.exp_pos _)

#print axioms hpThetaTrace_polynomial_pos
#print axioms hpThetaTrace_exp_polynomial_pos
#print axioms hpThetaTrace_exp_weighted_term_pos

#print hpThetaGaussianParameter
#print hpThetaGaussianProfile
#print hpThetaGaussianKernelTerm

#check hpRiemannThetaDifferentialKernel_hasSum
#check hpRiemannThetaDifferentialKernel_series_summable
#check hpRiemannThetaDifferentialKernel_eq_tsum
#check hpRiemannThetaDifferentialKernel_eq_explicit_series

end HodgeProofHP
LEAN

lake env lean "$target"
lake build HodgeProofHP.Stage4ThetaTraceTermPositivity

echo "PASS: Stage4ThetaTraceTermPositivity"
