#!/usr/bin/env bash
set -euo pipefail

file="HodgeProofHP/Stage3SchwartzQuadraticTerm.lean"

if [[ ! -f HodgeProofHP/Stage3SchwartzKineticTerm.lean ]]; then
  echo "STOP: run from the hodgeproof-hp repository root."
  exit 1
fi

if [[ -e "$file" ]]; then
  echo "STOP: $file already exists; no file was replaced."
  exit 1
fi

cat > "$file" <<'LEAN'
import HodgeProofHP.Stage3SchwartzKineticTerm
import Mathlib.Analysis.Normed.Operator.Mul

/-!
Stage 3.3: construct coordinate multiplication on Schwartz space,
then compose it twice for the quadratic term.
-/

namespace HodgeProofHP

/-- Coordinate multiplication on complex Schwartz functions. -/
noncomputable def hpSchwartzCoordinateMul :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  (SchwartzMap.evalCLM ℂ ℝ ℂ (1 : ℝ)).comp
    (SchwartzMap.smulRightCLM ℂ ℂ
      (ContinuousLinearMap.mul ℝ ℝ))

/-- Apply coordinate multiplication twice on Schwartz space. -/
noncomputable def hpSchwartzQuadraticMul :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  hpSchwartzCoordinateMul.comp hpSchwartzCoordinateMul

/-- The resulting quadratic term as an L²-valued linear map. -/
noncomputable def hpSchwartzQuadraticToL2 :
    SchwartzMap ℝ ℂ →L[ℂ] HPSpace :=
  hpSchwartzToL2.comp hpSchwartzQuadraticMul

#check hpSchwartzCoordinateMul
#check hpSchwartzQuadraticMul
#check hpSchwartzQuadraticToL2
#print axioms hpSchwartzQuadraticToL2

end HodgeProofHP
LEAN

lake build HodgeProofHP.Stage3SchwartzQuadraticTerm
lake env lean "$file"
