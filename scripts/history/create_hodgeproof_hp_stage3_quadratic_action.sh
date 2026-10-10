#!/usr/bin/env bash
set -euo pipefail

file="HodgeProofHP/Stage3SchwartzQuadraticAction.lean"

if [[ ! -f HodgeProofHP/Stage3SchwartzQuadraticTerm.lean ]]; then
  echo "STOP: run from the hodgeproof-hp repository root."
  exit 1
fi

if [[ -e "$file" ]]; then
  echo "STOP: $file already exists; no file was replaced."
  exit 1
fi

cat > "$file" <<'LEAN'
import HodgeProofHP.Stage3SchwartzQuadraticTerm

/-! Stage 3.4: pointwise action of the Schwartz multiplication maps. -/

namespace HodgeProofHP

/-- The first map multiplies by the real coordinate. -/
theorem hpSchwartzCoordinateMul_apply
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    (hpSchwartzCoordinateMul f) x = x • f x := by
  simp [hpSchwartzCoordinateMul, ContinuousLinearMap.mul_apply']

/-- Applying the first map twice multiplies by the quadratic potential. -/
theorem hpSchwartzQuadraticMul_apply
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    (hpSchwartzQuadraticMul f) x =
      hpQuadraticPotential x • f x := by
  change (hpSchwartzCoordinateMul
    (hpSchwartzCoordinateMul f)) x = _
  rw [hpSchwartzCoordinateMul_apply, hpSchwartzCoordinateMul_apply]
  simp [hpQuadraticPotential, pow_two, mul_smul]

#check hpSchwartzCoordinateMul_apply
#check hpSchwartzQuadraticMul_apply
#print axioms hpSchwartzQuadraticMul_apply

end HodgeProofHP
LEAN

lake build HodgeProofHP.Stage3SchwartzQuadraticAction
lake env lean "$file"
