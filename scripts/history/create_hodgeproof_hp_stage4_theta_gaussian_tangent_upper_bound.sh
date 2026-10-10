#!/usr/bin/env bash
set -euo pipefail

command -v lake >/dev/null || {
  echo "ERROR: lake not found"
  exit 1
}

lake build HodgeProofHP.Stage4ThetaSecondMomentProfileBound

python - <<'PY'
from pathlib import Path
from datetime import datetime

path = Path("HodgeProofHP/Stage4ThetaGaussianTangentUpperBound.lean")
if path.exists():
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
    backup = path.with_name(path.name + ".before_create_" + stamp)
    backup.write_bytes(path.read_bytes())
    print(f"BACKUP: {backup}")
path.parent.mkdir(parents=True, exist_ok=True)
PY

cat > HodgeProofHP/Stage4ThetaGaussianTangentUpperBound.lean <<'LEAN'
import HodgeProofHP.Stage4ThetaSecondMomentProfileBound

/-!
Exponential upper envelopes for the Gaussian theta profile terms,
obtained from tangent lower bounds for the exponential function.
-/

namespace HodgeProofHP

noncomputable def hpThetaGaussianTangentEnvelope
    (a l u : ℝ) : ℝ :=
  2 * Real.exp (l / 2 - a * Real.exp (2 * l)) *
    Real.exp (-(2 * a * Real.exp (2 * l) - 1 / 2) * (u - l))

theorem hpThetaGaussian_exp_two_mul_tangent_lower
    (l u : ℝ) :
    Real.exp (2 * l) * (1 + 2 * (u - l)) ≤
      Real.exp (2 * u) := by
  have ht :
      1 + 2 * (u - l) ≤ Real.exp (2 * (u - l)) := by
    linarith [Real.add_one_le_exp (2 * (u - l))]
  calc
    Real.exp (2 * l) * (1 + 2 * (u - l)) ≤
        Real.exp (2 * l) * Real.exp (2 * (u - l)) :=
      mul_le_mul_of_nonneg_left ht
        (le_of_lt (Real.exp_pos (2 * l)))
    _ = Real.exp (2 * u) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem hpThetaGaussianProfile_le_tangentEnvelope
    (a l u : ℝ) (ha : 0 ≤ a) :
    hpThetaGaussianProfile a u ≤
      hpThetaGaussianTangentEnvelope a l u := by
  have hscaled :=
    mul_le_mul_of_nonneg_left
      (hpThetaGaussian_exp_two_mul_tangent_lower l u) ha
  unfold hpThetaGaussianProfile hpThetaGaussianTangentEnvelope
  rw [mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  nlinarith [hscaled]

theorem hpThetaGaussianSeriesTerm_le_tangentEnvelope
    (n : ℕ) (l u : ℝ) :
    hpThetaGaussianProfile (hpThetaGaussianParameter n) u ≤
      hpThetaGaussianTangentEnvelope
        (hpThetaGaussianParameter n) l u := by
  apply hpThetaGaussianProfile_le_tangentEnvelope
  unfold hpThetaGaussianParameter
  positivity

theorem hpThetaGaussianTangentEnvelope_nonneg
    (a l u : ℝ) :
    0 ≤ hpThetaGaussianTangentEnvelope a l u := by
  unfold hpThetaGaussianTangentEnvelope
  positivity

#print axioms hpThetaGaussian_exp_two_mul_tangent_lower
#print axioms hpThetaGaussianProfile_le_tangentEnvelope
#print axioms hpThetaGaussianSeriesTerm_le_tangentEnvelope
#print axioms hpThetaGaussianTangentEnvelope_nonneg

end HodgeProofHP
LEAN

lake env lean HodgeProofHP/Stage4ThetaGaussianTangentUpperBound.lean
lake build HodgeProofHP.Stage4ThetaGaussianTangentUpperBound

echo "PASS: Stage4ThetaGaussianTangentUpperBound"
